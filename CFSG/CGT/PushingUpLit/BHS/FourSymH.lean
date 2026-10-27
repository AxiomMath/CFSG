module

public import CFSG.CGT.PushingUpLit.BHS.FourSymG
public import CFSG.CGT.PushingUpLit.BHS.FourSymF

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.Permutation.SymmetricCoxeter

variable {V : Type} [CommGroup V] [Finite V]

section Pivot

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem exists_pivot_pair (h : Hyp42 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) :
    ∃ A ∈ D, A ≤ T ∧ ∃ L ∈ lamSet P D M, A ≤ L ∧ ¬ L ≤ M ∧
      ∃ D₁ ∈ D, D₁ ≤ L ∧ D₁ ≠ A ∧ ¬ D₁ ≤ M ∧ L = A ⊔ D₁ ∧ NonComm A D₁ := by
  obtain ⟨A, hAD, hAT, L, hL, hAL, hLM⟩ := exists_pivot h hV
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := id hL
  have hAS : IsSylowOf 2 A L := (hΛ2 A).1 ⟨hAD, hAL⟩
  obtain ⟨S', hS', hne⟩ := hSL.exists_sylow_ne hn1 hAS
  have hS'D : S' ∈ D := ((hΛ2 S').2 hS').1
  have hsup : A ⊔ S' = L := hSL.sylow_sup_eq hn1 hAS hS' hne.symm
  refine ⟨A, hAD, hAT, L, ?_, hAL, hLM, S', hS'D, hS'.1, hne, fun hle => hLM ?_, hsup.symm,
    hSL.nonComm_of_sylow_ne hn1 hAS hS' hne.symm (h.ne_bot A hAD)⟩
  · exact hL
  · rw [← hsup]
    exact sup_le (hAT.trans h.le_M) hle

end Pivot

section CaseX

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem symCaseX (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hP : P = ⨆ X ∈ D, X) (hS2 : ∀ X ∈ D, Nat.card X = 2) (hconn : ConnD D)
    {A L D₁ : Subgroup (MulAut V)} (hAD : A ∈ D) (hAM : A ≤ M) (hL : L ∈ lamSet P D M)
    (hAL : A ≤ L) (hLM : ¬ L ≤ M) (hD₁D : D₁ ∈ D) (hD₁A : D₁ ≠ A) (hLeq : L = A ⊔ D₁)
    (hnc : NonComm A D₁)
    (hX : ∀ B ∈ D, B ≠ A → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B ≤ M) :
    Nonempty (SymData M D P 3) := by
  have hcen : ∀ B ∈ D, B ≠ A → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := fun B hB hne hc =>
    four_fifteen_M h hV hAD hB hAM (hX B hB hne hc) hne.symm hc hL hAL hLM
  have hcov := four_thirteen_conn h.toHyp42 hV hL hAD hAL hcen hconn
  have hPL : P = L := le_antisymm (hP.le.trans (iSup₂_le hcov)) hL.1
  obtain ⟨a, ua, ha, -, hAa, -⟩ := exists_transv_of_card_two h.toHyp41 hV hAD (hS2 A hAD)
  obtain ⟨d, ud, hd, -, hDd, -⟩ := exists_transv_of_card_two h.toHyp41 hV hD₁D (hS2 D₁ hD₁D)
  have hadj : d * a ≠ a * d := fun hc => by
    obtain ⟨a', ha', d', hd', hne⟩ := hnc
    rw [hAa] at ha'
    rw [hDd] at hd'
    exact hne ((forall_comm_zpowers_iff a d).2 hc.symm a' ha' d' hd')
  have hda : d ≠ a := gen_ne_of_ne hDd hAa hD₁A
  refine symData_of_chain h.toHyp42 hV hconn (k := 2) even_two le_rfl
    (fun i => if i = 0 then d else a) (fun i => if i = 0 then ud else ua) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    by_cases hi0 : i = 0
    · simp only [hi0, ite_true]
      exact hd
    · simp only [hi0, ite_false]
      exact ha
  · intro i hi
    by_cases hi0 : i = 0
    · simp only [hi0, ite_true, ← hDd]
      exact hD₁D
    · simp only [hi0, ite_false, ← hAa]
      exact hAD
  · intro i hi
    have : i = 0 := by omega
    subst this
    simpa using hadj
  · intro i j hij hj
    omega
  · intro i hi j hj hne
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact absurd rfl hne
    · simpa using hda
    · simpa using hda.symm
    · exact absurd rfl hne
  · refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨i, hi, rfl⟩
      by_cases hi0 : i = 0
      · simp only [hi0, ite_true]
        rw [hPL, hLeq]
        exact Subgroup.mem_sup_right (hDd ▸ Subgroup.mem_zpowers d)
      · simp only [hi0, ite_false]
        rw [hPL, hLeq]
        exact Subgroup.mem_sup_left (hAa ▸ Subgroup.mem_zpowers a)
    · rw [hPL, hLeq]
      refine sup_le ?_ ?_
      · rw [hAa, Subgroup.zpowers_le]
        exact Subgroup.subset_closure ⟨1, by norm_num, by simp⟩
      · rw [hDd, Subgroup.zpowers_le]
        exact Subgroup.subset_closure ⟨0, by norm_num, by simp⟩

end CaseX

section CaseY

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem symCaseY (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hP : P = ⨆ X ∈ D, X) (hS2 : ∀ X ∈ D, Nat.card X = 2) (hconn : ConnD D)
    {A L D₁ : Subgroup (MulAut V)} (hAD : A ∈ D) (hAT : A ≤ T) (hL : L ∈ lamSet P D M)
    (hAL : A ≤ L) (hLM : ¬ L ≤ M) (hD₁D : D₁ ∈ D) (hD₁A : D₁ ≠ A)
    (hLeq : L = A ⊔ D₁) (hnc : NonComm A D₁)
    (hY : ∃ B ∈ D, B ≠ A ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ ¬ B ≤ M)
    (IH : ∀ (P' : Subgroup (MulAut V)) (D' : Set (Subgroup (MulAut V)))
      (T' M' : Subgroup (MulAut V)), Nat.card P' < Nat.card P → Hyp43 P' D' T' M' →
      P' = ⨆ X ∈ D', X → (∀ X ∈ D', Nat.card X = 2) → ConnD D' →
      ∃ m, Nonempty (SymData M' D' P' m)) :
    ∃ m, Nonempty (SymData M D P m) := by
  have hAM : A ≤ M := hAT.trans h.le_M
  set H : Subgroup (MulAut V) := P ⊓ Subgroup.centralizer (A : Set (MulAut V)) with hHdef
  have hHP : H ≤ P := inf_le_left
  have hT : dInter D T ⊆ dInter D H := by
    intro X hX
    refine ⟨hX.1, le_inf (h.le X hX.1) fun x hx => Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact h.toHyp41.four_seven_pairs h.syl A ⟨hAD, hAT⟩ X hX a ha x hx
  obtain ⟨B₀, hB₀D, hB₀A, hB₀c, hB₀M⟩ := hY
  have hB₀cen : B₀ ∈ cenD D A := ⟨hB₀D, hB₀A, fun x hx a ha => (hB₀c a ha x hx).symm⟩
  have hM : ¬ dInter D H ⊆ dInter D M := fun hsub =>
    hB₀M (hsub ⟨hB₀D, le_inf (h.le B₀ hB₀D) (le_centralizer_of_mem_cenD hB₀cen)⟩).2
  obtain ⟨T₀, hT₀d, hH42⟩ := four_nine h.toHyp42 hHP hT hM
  have hDAsub : cenD D A ⊆ dInter D H := fun X hX =>
    ⟨hX.1, le_inf (h.le X hX.1) (le_centralizer_of_mem_cenD hX)⟩
  have hDAnorm : ∀ X ∈ cenD D A, ∀ g ∈ H, conjSub g X ∈ cenD D A := fun X hX g hg =>
    cenD_conj_of_cen h.toHyp41 hg.1
      (fun a ha => (Subgroup.mem_centralizer_iff.1 hg.2 a ha).symm) hX
  have hDAcore : ¬ cenD D A ⊆ dCore H (dInter D H) (M ⊓ H) := fun hsub => by
    have := (hsub hB₀cen).2 1 (Subgroup.one_mem _)
    rw [conjSub_one] at this
    exact hB₀M (this.trans inf_le_left)
  obtain ⟨T₁, hE42⟩ := four_ten hH42 hDAsub hDAnorm hDAcore
  set E' : Subgroup (MulAut V) := ⨆ X ∈ cenD D A, X with hE'def
  have hE'H : E' ≤ H := iSup₂_le fun X hX => (hDAsub hX).2
  have hE'P : E' ≤ P := hE'H.trans hHP
  have hh43 : Hyp43 E' (cenD D A) T₁ ((M ⊓ H) ⊓ E') :=
    ⟨hE42, fun X hX Z hZ hZE => h.max X hX.1 Z hZ (hZE.trans hE'P)⟩
  have hcard : Nat.card E' < Nat.card P := by
    have hne : H ≠ P := by
      intro heq
      obtain ⟨a, ha, d, hd, hne⟩ := hnc
      have hdP : d ∈ P := h.le D₁ hD₁D hd
      have hdH : d ∈ H := heq ▸ hdP
      exact hne ((Subgroup.mem_centralizer_iff.1 hdH.2 a ha))
    exact lt_of_le_of_lt (Subgroup.card_le_of_le hE'H) (FourOneTools.card_lt_of_le_of_ne hHP hne)
  have hconnDA : ConnD (cenD D A) :=
    connIn_cenD h hV hS2 hconn hP.le hAD hAM hH42.syl (hH42.le_M.trans inf_le_left)
  obtain ⟨n, ⟨d'⟩⟩ := IH E' (cenD D A) T₁ ((M ⊓ H) ⊓ E') hcard hh43 rfl
    (fun X hX => hS2 X hX.1) hconnDA
  obtain ⟨a, ua, ha, -, hAa, -⟩ := exists_transv_of_card_two h.toHyp41 hV hAD (hS2 A hAD)
  obtain ⟨d, ud, hd, -, hDd, -⟩ := exists_transv_of_card_two h.toHyp41 hV hD₁D (hS2 D₁ hD₁D)
  have hda : d ≠ a := gen_ne_of_ne hDd hAa hD₁A
  have hadnc : a * d ≠ d * a := fun hc => by
    obtain ⟨a', ha', d', hd', hne⟩ := hnc
    rw [hAa] at ha'
    rw [hDd] at hd'
    exact hne ((forall_comm_zpowers_iff a d).2 hc a' ha' d' hd')
  have haA : a ∈ A := hAa ▸ Subgroup.mem_zpowers a
  have hdD₁ : d ∈ D₁ := hDd ▸ Subgroup.mem_zpowers d
  obtain ⟨i₀, hi₀⟩ := d'.pt
  obtain ⟨y, u, hyT, hyadj, hyfar, hyne, hygen, hyfix⟩ :=
    d'.toSymCore.exists_chain hE42.toHyp41 hV (fun B hB => hS2 B hB.1) i₀
  have hn3 : 3 ≤ n := d'.three_le
  have hnodd : Odd n := d'.odd
  have hyM : ∀ i, i + 2 < n → y i ∈ M := by
    intro i hi
    have hi' : i < n - 1 := by omega
    obtain ⟨-, hyE, -⟩ := hyT i hi'
    have h1 := (hyfix i hi' hyE).2 (by omega)
    exact ((hi₀ ⟨y i, hyE⟩).2 h1).1.1
  have hyD : ∀ i, i < n - 1 → Subgroup.zpowers (y i) ∈ cenD D A := fun i hi => (hyT i hi).2.2
  have hyA : ∀ i, i < n - 1 → y i * a = a * y i := fun i hi =>
    (hyD i hi).2.2 (y i) (Subgroup.mem_zpowers _) a haA
  have hyd : ∀ i, i + 2 < n → y i * d = d * y i := by
    intro i hi
    have hi' : i < n - 1 := by omega
    have hBcen := hyD i hi'
    have hBM : Subgroup.zpowers (y i) ≤ M := (Subgroup.zpowers_le).2 (hyM i hi)
    have h1 := four_fifteen_M h hV hAD hBcen.1 hAM hBM hBcen.2.1.symm
      (fun a' ha' b hb => (hBcen.2.2 b hb a' ha').symm) hL hAL hLM d
      (hLeq ▸ Subgroup.mem_sup_right hdD₁) (y i) (Subgroup.mem_zpowers _)
    exact h1.symm
  have hlast : y (n - 2) * d ≠ d * y (n - 2) := by
    intro hc
    have hdall : ∀ i, i < n - 1 → y i * d = d * y i := by
      intro i hi
      by_cases hi2 : i + 2 < n
      · exact hyd i hi2
      · have : i = n - 2 := by omega
        rw [this]
        exact hc
    have hcentral : E' ≤ Subgroup.centralizer ({d} : Set (MulAut V)) := by
      rw [← hygen]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, hi, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hdall i hi)
    have hX : ∀ B ∈ D, B ≠ A → (∀ a' ∈ A, ∀ b ∈ B, a' * b = b * a') →
        ∀ l ∈ L, ∀ b ∈ B, l * b = b * l := by
      intro B hB hne hcB l hl b hb
      have hBcen : B ∈ cenD D A := ⟨hB, hne, fun x hx a' ha' => (hcB a' ha' x hx).symm⟩
      have hbE : b ∈ E' :=
        (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ cenD D A) => X) B hBcen
          le_rfl) hb
      have hbd : b * d = d * b := Subgroup.mem_centralizer_singleton_iff.1 (hcentral hbE)
      have hAle : A ≤ Subgroup.centralizer ({b} : Set (MulAut V)) := fun a' ha' =>
        Subgroup.mem_centralizer_singleton_iff.2 (hcB a' ha' b hb)
      have hDle : D₁ ≤ Subgroup.centralizer ({b} : Set (MulAut V)) := by
        intro d' hd'
        rw [hDd] at hd'
        obtain ⟨k, rfl⟩ := hd'
        exact Subgroup.mem_centralizer_singleton_iff.2
          (Commute.zpow_right (show Commute b d from hbd) k).eq.symm
      have hLle : L ≤ Subgroup.centralizer ({b} : Set (MulAut V)) := by
        rw [hLeq]
        exact sup_le hAle hDle
      exact Subgroup.mem_centralizer_singleton_iff.1 (hLle hl)
    have hcov := four_thirteen_conn h.toHyp42 hV hL hAD hAL hX hconn
    obtain ⟨-, ⟨n', hn1, hSL⟩, hΛ2, -⟩ := id hL
    have hB₀S : IsSylowOf 2 B₀ L := (hΛ2 B₀).1 ⟨hB₀D, hcov B₀ hB₀D⟩
    have hAS : IsSylowOf 2 A L := (hΛ2 A).1 ⟨hAD, hAL⟩
    obtain ⟨a', ha', b', hb', hne⟩ :=
      hSL.nonComm_of_sylow_ne hn1 hAS hB₀S hB₀A.symm (h.ne_bot A hAD)
    exact hne (hB₀c a' ha' b' hb')
  set x : ℕ → MulAut V := fun i => if i < n - 1 then y i else if i = n - 1 then d else a
    with hxdef
  set uu : ℕ → V := fun i => if i < n - 1 then u i else if i = n - 1 then ud else ua
    with huudef
  have hxlt : ∀ i, i < n - 1 → x i = y i := fun i hi => by simp [hxdef, hi]
  have hxmid : x (n - 1) = d := by simp [hxdef]
  have hxlast : x n = a := by
    have h1 : ¬ n < n - 1 := by omega
    have h2 : n ≠ n - 1 := by omega
    simp [hxdef, h1, h2]
  have huult : ∀ i, i < n - 1 → uu i = u i := fun i hi => by simp [huudef, hi]
  have huumid : uu (n - 1) = ud := by simp [huudef]
  have huulast : uu n = ua := by
    have h1 : ¬ n < n - 1 := by omega
    have h2 : n ≠ n - 1 := by omega
    simp [huudef, h1, h2]
  have hyd1 : ∀ i, i < n - 1 → y i ≠ d := fun i hi e => hadnc (by
    have := hyA i hi
    rw [e] at this
    exact this.symm)
  have hya1 : ∀ i, i < n - 1 → y i ≠ a := fun i hi e => (hyD i hi).2.1 (by rw [e, ← hAa])
  refine ⟨n + 1 + 1, symData_of_chain h.toHyp42 hV hconn (k := n + 1) hnodd.add_one (by omega) x
    uu ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro i hi
    rcases lt_trichotomy i (n - 1) with hlt | heq | hgt
    · rw [hxlt i hlt, huult i hlt]
      exact (hyT i hlt).1
    · subst heq
      rw [hxmid, huumid]
      exact hd
    · have : i = n := by omega
      subst this
      rw [hxlast, huulast]
      exact ha
  · intro i hi
    rcases lt_trichotomy i (n - 1) with hlt | heq | hgt
    · rw [hxlt i hlt]
      exact (hyD i hlt).1
    · subst heq
      rw [hxmid, ← hDd]
      exact hD₁D
    · have : i = n := by omega
      subst this
      rw [hxlast, ← hAa]
      exact hAD
  · intro i hi
    rcases lt_trichotomy (i + 1) (n - 1) with hlt | heq | hgt
    · rw [hxlt i (by omega), hxlt (i + 1) hlt]
      exact hyadj i hlt
    · have hi2 : i = n - 2 := by omega
      rw [hxlt i (by omega), heq, hxmid, hi2]
      exact hlast
    · have hi2 : i = n - 1 := by omega
      subst hi2
      have e : n - 1 + 1 = n := by omega
      rw [hxmid, e, hxlast]
      exact fun hc => hadnc hc.symm
  · intro i j hij hj
    rcases lt_trichotomy j (n - 1) with hlt | heq | hgt
    · rw [hxlt i (by omega), hxlt j hlt]
      exact hyfar i j hij hlt
    · subst heq
      rw [hxlt i (by omega), hxmid]
      exact hyd i (by omega)
    · have : j = n := by omega
      subst this
      rw [hxlast, hxlt i (by omega)]
      exact hyA i (by omega)
  · have hne' : ∀ i j, i < n + 1 → j < n + 1 → i < j → x i ≠ x j := by
      intro i j hi hj hij
      rcases lt_trichotomy j (n - 1) with hlt | heq | hgt
      · rw [hxlt i (by omega), hxlt j hlt]
        exact hyne i (by omega) j hlt (by omega)
      · subst heq
        rw [hxlt i (by omega), hxmid]
        exact hyd1 i (by omega)
      · have hjn : j = n := by omega
        have hxj : x j = a := by rw [hjn]; exact hxlast
        rw [hxj]
        by_cases hin : i < n - 1
        · rw [hxlt i hin]
          exact hya1 i hin
        · have : i = n - 1 := by omega
          subst this
          rw [hxmid]
          exact hda
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h1 | h1
    · exact hne' i j hi hj h1
    · exact (hne' j i hj hi h1).symm
  · have hxU : ∀ i, i < n + 1 → x i ∈ Subgroup.closure (x '' Set.Iio (n + 1)) := fun i hi =>
      Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hdU : d ∈ Subgroup.closure (x '' Set.Iio (n + 1)) := hxmid ▸ hxU (n - 1) (by omega)
    have haU : a ∈ Subgroup.closure (x '' Set.Iio (n + 1)) := hxlast ▸ hxU n (by omega)
    have hLU : L ≤ Subgroup.closure (x '' Set.Iio (n + 1)) := by
      rw [hLeq, hAa, hDd]
      exact sup_le ((Subgroup.zpowers_le).2 haU) ((Subgroup.zpowers_le).2 hdU)
    have hE'U : E' ≤ Subgroup.closure (x '' Set.Iio (n + 1)) := by
      rw [← hygen]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < n - 1 := hi
      rw [← hxlt i hi']
      exact hxU i (by omega)
    have hcover : ∀ B ∈ D, (∀ a' ∈ A, ∀ b ∈ B, a' * b = b * a') →
        B ≤ Subgroup.closure (x '' Set.Iio (n + 1)) := by
      intro B hB hcB
      by_cases hBA : B = A
      · rw [hBA]
        exact hAL.trans hLU
      · exact (le_iSup₂_of_le (f := fun (X : Subgroup (MulAut V)) (_ : X ∈ cenD D A) => X) B
          ⟨hB, hBA, fun x hx a' ha' => (hcB a' ha' x hx).symm⟩ le_rfl).trans hE'U
    have hall := four_thirteen_cover h.toHyp42 hV hL hLU hAD hAL hcover
    have hUP : Subgroup.closure (x '' Set.Iio (n + 1)) ≤ P := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < n + 1 := hi
      rcases lt_trichotomy i (n - 1) with hlt | heq | hgt
      · rw [hxlt i hlt]
        exact hE'P (hyT i hlt).2.1
      · subst heq
        rw [hxmid]
        exact h.le D₁ hD₁D hdD₁
      · have : i = n := by omega
        subst this
        rw [hxlast]
        exact h.le A hAD haA
    exact le_antisymm hUP (hP.le.trans (iSup₂_le hall))

end CaseY

section Main

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

theorem symStep (h : Hyp43 P D T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hP : P = ⨆ X ∈ D, X) (hS2 : ∀ X ∈ D, Nat.card X = 2) (hconn : ConnD D)
    (IH : ∀ (P' : Subgroup (MulAut V)) (D' : Set (Subgroup (MulAut V)))
      (T' M' : Subgroup (MulAut V)), Nat.card P' < Nat.card P → Hyp43 P' D' T' M' →
      P' = ⨆ X ∈ D', X → (∀ X ∈ D', Nat.card X = 2) → ConnD D' →
      ∃ m, Nonempty (SymData M' D' P' m)) :
    ∃ m, Nonempty (SymData M D P m) := by
  obtain ⟨A, hAD, hAT, L, hL, hAL, hLM, D₁, hD₁D, -, hD₁A, -, hLeq, hnc⟩ :=
    exists_pivot_pair h.toHyp42 hV
  have hAM : A ≤ M := hAT.trans h.le_M
  by_cases hX : ∀ B ∈ D, B ≠ A → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B ≤ M
  · exact ⟨3, symCaseX h hV hP hS2 hconn hAD hAM hL hAL hLM hD₁D hD₁A hLeq hnc hX⟩
  · push Not at hX
    exact symCaseY h hV hP hS2 hconn hAD hAT hL hAL hLM hD₁D hD₁A hLeq hnc hX IH

theorem symMain (hV : ∀ v : V, v ^ 2 = 1) :
    ∀ (N : ℕ) (P : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
      (T M : Subgroup (MulAut V)), Nat.card P ≤ N → Hyp43 P D T M → P = ⨆ X ∈ D, X →
      (∀ X ∈ D, Nat.card X = 2) → ConnD D → ∃ m, Nonempty (SymData M D P m) := by
  intro N
  induction N with
  | zero =>
    intro P D T M hN
    exfalso
    have := Nat.card_pos (α := ↥P)
    omega
  | succ N ih =>
    intro P D T M hN h hP hS2 hconn
    exact symStep h hV hP hS2 hconn fun P' D' T' M' hlt =>
      ih P' D' T' M' (by omega)

end Main

end CFSG.CGT.PushingUpLit.BHS

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutRank

public section

namespace CFSG.QuasithinUnique.Setup.X3Aut

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def ShortGen (G : Type*) [Group G] (I : Subgroup G) : Prop :=
  ∀ A : Subgroup G, A ≠ ⊥ → CFSG.IsElementaryAbelian 2 ↥A →
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ c : Fin m → G, (∀ i, c i ∈ I) ∧
        I ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (c i)).toMonoidHom : Subgroup G) : Set G))

@[expose] def PslSub : Subgroup AutA6 := A6Models.psl29.subgroupOf A6Models.autA6

theorem mem_PslSub {x : AutA6} : x ∈ PslSub ↔ (x : P10) ∈ A6Models.psl29 := Iff.rfl

theorem PslSub_normal {g : AutA6} {z : AutA6} (hz : z ∈ PslSub) : g * z * g⁻¹ ∈ PslSub := by
  rw [mem_PslSub] at hz ⊢
  exact psl29_normal _ g.2 _ hz

theorem evalWord_foldl {P : List ℕ → Prop} (hcid : P Core.cid)
    (hmul : ∀ a b, P a → P b → P (Core.cmul a b)) (X : List (List ℕ)) (hX : ∀ x ∈ X, P x) :
    ∀ (w : List ℕ) (acc : List ℕ), P acc →
      P (w.foldl (fun acc i => Core.cmul acc (X.getD i Core.cid)) acc)
  | [], _, h => h
  | i :: w, acc, h => by
    apply evalWord_foldl hcid hmul X hX w
    apply hmul _ _ h
    by_cases hi : i < X.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hX _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.mp hi)]; exact hcid

theorem evalWord_mem {P : List ℕ → Prop} (hcid : P Core.cid)
    (hmul : ∀ a b, P a → P b → P (Core.cmul a b)) (X : List (List ℕ)) (hX : ∀ x ∈ X, P x)
    (w : List ℕ) : P (evalWord X w) :=
  evalWord_foldl hcid hmul X hX w Core.cid hcid

theorem witOK_spec {E : List (List ℕ)} {r : ℕ} {S : List ℕ} {W : List (List ℕ)}
    (h : witOK E r S W = true) :
    (∀ i ∈ S, i < Core.pslLit.length) ∧ S.length * r ≤ 6 ∧
      ∀ g ∈ Core.pslGenC, ∃ w, evalWord (witX E S) w = g := by
  unfold witOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hS, hsr⟩, hW⟩, hz⟩ := h
  refine ⟨fun i hi => of_decide_eq_true (List.all_eq_true.mp hS i hi), of_decide_eq_true hsr,
    fun g hg => ?_⟩
  obtain ⟨w, -, hp⟩ := exists_of_all_zip (fun g w => evalWord (witX E S) w == g) Core.pslGenC W
    hz (beq_iff_eq.mp hW).symm g hg
  exact ⟨w, beq_iff_eq.mp hp⟩

theorem PslSub_le_of_words {H : Subgroup AutA6} {n : AutA6} {X : List (List ℕ)}
    (hX : ∀ x ∈ X, ∃ y ∈ H, cd (n * y * n⁻¹) = x)
    (hw : ∀ g ∈ Core.pslGenC, ∃ w, evalWord X w = g) : PslSub ≤ H := by
  let Q : List ℕ → Prop := fun x => ∃ y ∈ H, cd (n * y * n⁻¹) = x
  have hQcid : Q Core.cid := ⟨1, H.one_mem, by simp [cd_one]⟩
  have hQmul : ∀ a b, Q a → Q b → Q (Core.cmul a b) := by
    rintro a b ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
    refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, ?_⟩
    rw [← cd_mul]; congr 1; group
  have hQgen : ∀ g ∈ Core.pslGenC, Q g := by
    intro g hg
    obtain ⟨w, hw'⟩ := hw g hg
    rw [← hw']
    exact evalWord_mem hQcid hQmul _ hX w
  have hgenH : ∀ t ∈ pslGens, ∀ ht : t ∈ A6Models.autA6, n⁻¹ * (⟨t, ht⟩ : AutA6) * n ∈ H := by
    intro t ht hta
    have hc : code t ∈ Core.pslGenC := by
      rw [← pslGens_code]; exact List.mem_map_of_mem ht
    obtain ⟨y, hy, hyc⟩ := hQgen _ hc
    have h1 : n * y * n⁻¹ = ⟨t, hta⟩ := cd_injective hyc
    have h2 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [← h1, ← h2]; exact hy
  have hall : ∀ y : P10, y ∈ Subgroup.closure {g | g ∈ pslGens} → ∀ hya : y ∈ A6Models.autA6,
      n⁻¹ * (⟨y, hya⟩ : AutA6) * n ∈ H := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact fun hya => hgenH t ht hya
    | one =>
      intro hya
      have h1 : (⟨1, hya⟩ : AutA6) = 1 := rfl
      rw [h1, mul_one, inv_mul_cancel]
      exact H.one_mem
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      intro hya
      have h1 : y₁ ∈ A6Models.autA6 := psl29_le_autA6 (by rw [psl29_eq]; exact hy₁)
      have h2 : y₂ ∈ A6Models.autA6 := psl29_le_autA6 (by rw [psl29_eq]; exact hy₂)
      have e : (⟨y₁ * y₂, hya⟩ : AutA6) = ⟨y₁, h1⟩ * ⟨y₂, h2⟩ := rfl
      have e2 : n⁻¹ * (⟨y₁, h1⟩ * ⟨y₂, h2⟩ : AutA6) * n =
          (n⁻¹ * ⟨y₁, h1⟩ * n) * (n⁻¹ * ⟨y₂, h2⟩ * n) := by group
      rw [e, e2]
      exact H.mul_mem (ih₁ h1) (ih₂ h2)
    | inv y hy ih =>
      intro hya
      have h1 : y ∈ A6Models.autA6 := (Subgroup.inv_mem_iff _).mp hya
      have e : (⟨y⁻¹, hya⟩ : AutA6) = (⟨y, h1⟩ : AutA6)⁻¹ := rfl
      have e2 : n⁻¹ * (⟨y, h1⟩ : AutA6)⁻¹ * n = (n⁻¹ * ⟨y, h1⟩ * n)⁻¹ := by group
      rw [e, e2]
      exact H.inv_mem (ih h1)
  intro z hz'
  have hz1 : n * z * n⁻¹ ∈ PslSub := PslSub_normal hz'
  have hmem := hall (n * z * n⁻¹ : AutA6).1 (by rw [← psl29_eq]; exact hz1) (n * z * n⁻¹).2
  have e : n⁻¹ * (⟨(n * z * n⁻¹ : AutA6).1, (n * z * n⁻¹ : AutA6).2⟩ : AutA6) * n = z := by
    show n⁻¹ * (n * z * n⁻¹) * n = z
    group
  rw [← e]
  exact hmem

theorem shortGen_model : ShortGen AutA6 PslSub := by
  intro A hA hel
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (IsElementaryAbelian.isPGroup 2 ↥A).exists_card_eq
  obtain ⟨hr3, j, hj, hjlen, n, hn⟩ := rank_lemma r A hel hr
  have hr1 : 1 ≤ r := by
    by_contra h
    have h0 : r = 0 := by omega
    apply hA
    rw [h0, pow_zero] at hr
    exact Subgroup.card_eq_one.mp hr
  obtain ⟨hnd, hid, hlen', hinv, hclos, hrk⟩ := rep_spec hj
  have hrank : repRank.getD j 0 = r :=
    Nat.pow_right_injective (le_refl 2) (hlen'.symm.trans hjlen)
  have hsurj := conjInto_surj hnd (by rw [hr, hjlen]) hn
  obtain ⟨hSlt, hsr, hz⟩ := witOK_spec (wit_spec hj (by omega))
  rw [hrank] at hsr
  generalize witS.getD j [] = S at hSlt hsr hz
  generalize witW.getD j [] = W at hz
  have hsel : ∀ p : Fin S.length, ∃ s : AutA6, s ∈ PslSub ∧
      cd s = Core.pslLit.getD (S.getD p 0) Core.cid := by
    intro p
    obtain ⟨y, hy, hyc⟩ := exists_psl_getD (S.getD p 0)
    exact ⟨⟨y, psl29_le_autA6 hy⟩, hy, hyc⟩
  choose s hsP hsc using hsel
  let c : Fin S.length → AutA6 := fun p => n⁻¹ * s p * n
  have hcP : ∀ p, c p ∈ PslSub := fun p => by
    have := PslSub_normal (g := n⁻¹) (hsP p)
    simpa [c, inv_inv] using this
  refine ⟨r, S.length, hr, hr1, hr3, hsr, c, hcP, ?_⟩
  set H := Subgroup.closure (⋃ i : Fin S.length,
    ((A.map (MulAut.conj (c i)).toMonoidHom : Subgroup AutA6) : Set AutA6)) with hH
  have hQX : ∀ x ∈ witX (rep j) S, ∃ y ∈ H, cd (n * y * n⁻¹) = x := by
    intro x hx
    unfold witX at hx
    rw [List.mem_flatMap] at hx
    obtain ⟨s', hs', hx⟩ := hx
    rw [List.mem_map] at hx hs'
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := hs'
    obtain ⟨p, hpl, hpi⟩ := List.mem_iff_getElem.mp hi
    obtain ⟨a, haA, hae⟩ := hsurj e he
    have hi' : Core.pslLit.getD i Core.cid = cd (s ⟨p, hpl⟩) := by
      rw [hsc]; congr 1; rw [List.getD_eq_getElem _ _ hpl]; exact hpi.symm
    refine ⟨c ⟨p, hpl⟩ * a * (c ⟨p, hpl⟩)⁻¹, ?_, ?_⟩
    · apply Subgroup.subset_closure
      refine Set.mem_iUnion.mpr ⟨⟨p, hpl⟩, a, haA, ?_⟩
      simp [MulAut.conj_apply]
    · rw [hi', ← hae, ← cd_inv, ← cd_mul, ← cd_mul]
      congr 1
      simp only [c]; group
  exact PslSub_le_of_words hQX hz

theorem exists_pslSub_getD (i : ℕ) :
    ∃ s : AutA6, s ∈ PslSub ∧ cd s = Core.pslLit.getD i Core.cid := by
  obtain ⟨y, hy, hyc⟩ := exists_psl_getD i
  exact ⟨⟨y, psl29_le_autA6 hy⟩, hy, hyc⟩

theorem exists_zip_partner {α β : Type*} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → ∀ x ∈ l₁, ∃ y, (x, y) ∈ l₁.zip l₂
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: l₁, b :: l₂, hl, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := exists_zip_partner l₁ l₂ (by simpa using hl) x hx
      exact ⟨y, by simp [hy]⟩

set_option maxRecDepth 100000 in
theorem d3_model {a : AutA6} (ha : a ∈ PslSub) (ha1 : a ≠ 1) (haa : a * a = 1) :
    ∃ g : Fin 3 → AutA6, (∀ i, g i ∈ PslSub) ∧
      PslSub ≤ Subgroup.closure (Set.range fun i => g i * a * (g i)⁻¹) := by
  have h := d3Check_true
  unfold d3Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hHlen, hA0⟩, hpairs⟩, hinv0⟩, hG3⟩, hGlt⟩, hWlen⟩, hword⟩ := h
  have hHlen' : d3H.length = pslInvs.length := beq_iff_eq.mp hHlen
  have hG3' : d3G.length = 3 := beq_iff_eq.mp hG3
  have hWlen' : d3W.length = Core.pslGenC.length := beq_iff_eq.mp hWlen
  have hacode : cd a ∈ pslInvs := by
    unfold pslInvs
    rw [List.mem_filter]
    refine ⟨(mem_psl29_iff _).mp ha, ?_⟩
    unfold isInvC
    have h1 : Core.cmul (cd a) (cd a) = Core.cid := by rw [← cd_mul, haa, cd_one]
    have h2 : cd a ≠ Core.cid := fun h => ha1 (cd_injective (h.trans cd_one.symm))
    simp [h1, h2]
  obtain ⟨hh, hhmem⟩ := exists_zip_partner pslInvs d3H hHlen'.symm _ hacode
  have hpair := List.all_eq_true.mp hpairs _ hhmem
  rw [Bool.and_eq_true] at hpair
  have hhlt : hh < Core.pslLit.length := of_decide_eq_true hpair.1
  have hhconj := beq_iff_eq.mp hpair.2
  obtain ⟨h₀, hh₀P, hh₀c⟩ := exists_pslSub_getD hh
  obtain ⟨a₀, ha₀P, ha₀c⟩ := exists_pslSub_getD d3A0
  have hgam : ∀ i : Fin 3, ∃ s : AutA6, s ∈ PslSub ∧
      cd s = Core.pslLit.getD (d3G.getD i 0) Core.cid := fun i => exists_pslSub_getD _
  choose γ hγP hγc using hgam
  have hae : a = h₀ * a₀ * h₀⁻¹ := by
    apply cd_injective
    rw [cd_mul, cd_mul, cd_inv, hh₀c, ha₀c]
    exact hhconj.symm
  refine ⟨fun i => h₀ * γ i * h₀⁻¹, fun i => ?_, ?_⟩
  · exact PslSub.mul_mem (PslSub.mul_mem hh₀P (hγP i)) (PslSub.inv_mem hh₀P)
  · apply PslSub_le_of_words (n := h₀⁻¹)
      (X := d3G.map fun i => Core.cmul (Core.cmul (Core.pslLit.getD i Core.cid)
        (Core.pslLit.getD d3A0 Core.cid)) (invC (Core.pslLit.getD i Core.cid)))
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨p, hpl, hpi⟩ := List.mem_iff_getElem.mp hi
      have hp3 : p < 3 := hG3' ▸ hpl
      have hip : Core.pslLit.getD i Core.cid = cd (γ ⟨p, hp3⟩) := by
        rw [hγc]; congr 1; rw [List.getD_eq_getElem _ _ hpl]; exact hpi.symm
      refine ⟨(h₀ * γ ⟨p, hp3⟩ * h₀⁻¹) * a * (h₀ * γ ⟨p, hp3⟩ * h₀⁻¹)⁻¹, ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨⟨p, hp3⟩, rfl⟩
      · rw [hip, ← ha₀c, ← cd_inv, ← cd_mul, ← cd_mul, hae]
        congr 1
        group
    · intro g hg
      obtain ⟨w, -, hw⟩ := exists_of_all_zip (fun g w => evalWord (d3G.map fun i =>
        Core.cmul (Core.cmul (Core.pslLit.getD i Core.cid) (Core.pslLit.getD d3A0 Core.cid))
          (invC (Core.pslLit.getD i Core.cid))) w == g) Core.pslGenC d3W hword hWlen'.symm g hg
      exact ⟨w, beq_iff_eq.mp hw⟩

end CFSG.QuasithinUnique.Setup.X3Aut

module

public import CFSG.ClassicalInvolution.Q3.Sec13AECoverEven
public import CFSG.ClassicalInvolution.Q3.TL4AECoverM
public import CFSG.ClassicalInvolution.Q3.TL3T52A
public import CFSG.ClassicalInvolution.Q3.TL3T51B
public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8H

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

private theorem ae8b1_exists_avoid {n : ℕ} (s : Finset (Fin n)) (hs : s.card < n) :
    ∃ j : Fin n, j ∉ s := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ s := fun j _ => h j
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

private theorem ae8b1_cyc {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) i = j ∧ (Equiv.swap i j * Equiv.swap j k) j = k := by
  constructor
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]

private theorem ae8b1_cyc_fix {n : ℕ} {i j k x : Fin n} (h1 : x ≠ i) (h2 : x ≠ j) (h3 : x ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) x = x := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h2 h3,
    Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem ae8b1_cyc_sign {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) :
    Equiv.Perm.sign (Equiv.swap i j * Equiv.swap j k) = 1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap hjk]
  norm_num

theorem ae8b1_ofPerm_mem {n : ℕ} {c : Equiv.Perm (Fin n)} (hs : Equiv.Perm.sign c = 1) :
    AE.Wr.ofPerm c ∈ AE.aeSub n := by
  rw [AE.mem_aeSub]
  exact ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm], hs⟩

theorem ae8b1_core {n : ℕ} (hn : 5 ≤ n) (w : AE.Wr n)
    (hc : ∀ c : Equiv.Perm (Fin n), Equiv.Perm.sign c = 1 →
      w * AE.Wr.ofPerm c = AE.Wr.ofPerm c * w ∨
        AE.Wr.ofPerm c * w = w * AE.Wr.ofPerm c * AE.Wr.allOnes n) :
    w = 1 ∨ w = AE.Wr.allOnes n := by
  classical
  have hσ : ∀ c : Equiv.Perm (Fin n), Equiv.Perm.sign c = 1 → w.perm * c = c * w.perm := by
    intro c hs
    rcases hc c hs with h | h
    · have := congrArg AE.Wr.perm h
      simpa [AE.Wr.mul_perm, AE.Wr.ofPerm] using this
    · have := congrArg AE.Wr.perm h
      simpa [AE.Wr.mul_perm, AE.Wr.ofPerm, AE.Wr.allOnes] using this.symm
  have hfix : ∀ i, w.perm i = i := by
    intro i
    by_contra hi
    obtain ⟨j, hj⟩ := ae8b1_exists_avoid ({i, w.perm i} : Finset (Fin n))
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨k, hk⟩ := ae8b1_exists_avoid ({i, w.perm i, j} : Finset (Fin n))
      (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hj1, hj2⟩ := hj
    obtain ⟨hk1, hk2, hk3⟩ := hk
    have hij : i ≠ j := fun e => hj1 e.symm
    have hjk : j ≠ k := fun e => hk3 e.symm
    have hik : i ≠ k := fun e => hk1 e.symm
    obtain ⟨hci, hcj⟩ := ae8b1_cyc hij hjk hik
    have hcf : (Equiv.swap i j * Equiv.swap j k) (w.perm i) = w.perm i :=
      ae8b1_cyc_fix (fun e => hi e) (fun e => hj2 e.symm) (fun e => hk2 e.symm)
    have hcomm := hσ _ (ae8b1_cyc_sign hij hjk)
    have e1 : w.perm ((Equiv.swap i j * Equiv.swap j k) i) =
        (Equiv.swap i j * Equiv.swap j k) (w.perm i) :=
      congrArg (fun p : Equiv.Perm (Fin n) => p i) hcomm
    have e2 : w.perm ((Equiv.swap i j * Equiv.swap j k) j) =
        (Equiv.swap i j * Equiv.swap j k) (w.perm j) :=
      congrArg (fun p : Equiv.Perm (Fin n) => p j) hcomm
    rw [hci, hcf] at e1
    rw [hcj, e1, hcf] at e2
    have hjk' : w.perm j = w.perm k := by rw [e1, e2]
    exact hjk (w.perm.injective hjk')
  have hperm1 : w.perm = 1 := Equiv.ext fun x => hfix x
  have hvec : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      ∀ x, w.vec ((Equiv.swap i j * Equiv.swap j k).symm x) = w.vec x := by
    intro i j k hij hjk hik x
    obtain ⟨l, hl⟩ := ae8b1_exists_avoid ({i, j, k} : Finset (Fin n))
      (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    obtain ⟨hl1, hl2, hl3⟩ := hl
    have hcl : (Equiv.swap i j * Equiv.swap j k) l = l := ae8b1_cyc_fix hl1 hl2 hl3
    rcases hc _ (ae8b1_cyc_sign hij hjk) with h | h
    · have := congrArg (fun a : AE.Wr n => a.vec x) h
      simpa [AE.Wr.mul_vec, AE.Wr.ofPerm, hperm1] using this.symm
    · exfalso
      have := congrArg (fun a : AE.Wr n => a.vec l) h
      have hsl : (Equiv.swap i j * Equiv.swap j k).symm l = l :=
        (Equiv.symm_apply_eq _).mpr hcl.symm
      simp [AE.Wr.mul_vec, AE.Wr.ofPerm, AE.Wr.allOnes, hperm1, hsl] at this
  have hconst : ∀ a b : Fin n, w.vec a = w.vec b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨k, hk⟩ := ae8b1_exists_avoid ({a, b} : Finset (Fin n))
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hak, hbk⟩ := hk
    have hak' : a ≠ k := fun e => hak e.symm
    have hbk' : b ≠ k := fun e => hbk e.symm
    have hca := (ae8b1_cyc hab hbk' hak').1
    have hsb : (Equiv.swap a b * Equiv.swap b k).symm b = a :=
      (Equiv.symm_apply_eq _).mpr hca.symm
    have h := hvec a b k hab hbk' hak' b
    rw [hsb] at h
    exact h
  set a₀ := w.vec ⟨0, by omega⟩ with ha₀
  have hv : ∀ x, w.vec x = a₀ := fun x => hconst x _
  have hzmod : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hzmod a₀ with h0 | h1
  · left
    refine AE.Wr.ext ?_ (by rw [AE.Wr.one_perm]; exact hperm1)
    funext x
    rw [AE.Wr.one_vec, hv x, h0]
    rfl
  · right
    refine AE.Wr.ext ?_ (by rw [hperm1]; rfl)
    funext x
    rw [hv x, h1]
    rfl

theorem ae8b1_centre_aeSub {n : ℕ} (hn : 5 ≤ n) (w : AE.Wr n)
    (hc : ∀ a ∈ AE.aeSub n, w * a = a * w) : w = 1 ∨ w = AE.Wr.allOnes n :=
  ae8b1_core hn w fun c hs => Or.inl (hc _ (ae8b1_ofPerm_mem hs))

theorem ae8b1_centre_image {n : ℕ} (hn : 5 ≤ n) (x : AE.AEQ n)
    (hx : ∀ a ∈ AE.aeSub n, x * AE.mkQ n a = AE.mkQ n a * x) : x = 1 := by
  obtain ⟨w, hw⟩ : ∃ w : AE.Wr n, AE.mkQ n w = x := QuotientGroup.mk_surjective x
  subst hw
  have hc : ∀ c : Equiv.Perm (Fin n), Equiv.Perm.sign c = 1 →
      w * AE.Wr.ofPerm c = AE.Wr.ofPerm c * w ∨
        AE.Wr.ofPerm c * w = w * AE.Wr.ofPerm c * AE.Wr.allOnes n := by
    intro c hs
    have h := hx _ (ae8b1_ofPerm_mem hs)
    rw [← map_mul, ← map_mul] at h
    rcases AE.mkQ_eq_iff.mp h with h1 | h1
    · exact Or.inl (inv_mul_eq_one.mp h1)
    · exact Or.inr (inv_mul_eq_iff_eq_mul.mp h1)
  rcases ae8b1_core hn w hc with h1 | h1
  · rw [h1, map_one]
  · rw [h1]
    exact (QuotientGroup.eq_one_iff _).mpr (AE.mem_piSub.mpr (Or.inr rfl))

theorem ae8b1_memAt_inj {n : ℕ} (hn : 5 ≤ n) {s s' : Finset (Fin n)} {h : s.card = 4}
    {h' : s'.card = 4} {b b' : Bool} (e : AE.memAt s h b = AE.memAt s' h' b') :
    s = s' ∧ b = b' := by
  have em : AE.memBar s h b = AE.memBar s' h' b' := congrArg (Subgroup.map (AE.mkQ n)) e
  have hs : s = s' := AE.eq_of_memBar_eq' hn em
  subst hs
  refine ⟨rfl, ?_⟩
  by_contra hb
  cases b <;> cases b' <;> simp at hb
  · exact AE.memBar_true_ne_false hn s h (em.symm.trans (by rfl))
  · exact AE.memBar_true_ne_false hn s h em

theorem ae8b1_twin_of_comm (H : End18.Hyp Ω) {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω)
    (hc : Commutes A B) : B ∈ twinSet Ω A := by
  obtain ⟨zA, hzA⟩ := (H.endHyp.thmD.hyp.omega1 A hA).1
  obtain ⟨zB, hzB⟩ := (H.endHyp.thmD.hyp.omega1 B hB).1
  exact ⟨hB, zA, hzA, (H.perp9 A hA B hB hc zA zB hzA hzB) ▸ hzB⟩

private theorem ae8b1_oddCore (H : End18.Hyp Ω) (hu : SectData Ω u) :
    classicalInvolutionOddCore ↥(pSpan (Generic.centMembers Ω u)) = ⊥ := by
  have hu2 : u ∈ pCore 2 G := H.endHyp.zGroup_le_pCore hu.mem
  have h1 := TC.oddCoreImg_centralizer_eq_bot H.endHyp.thmD.odd
    (inferInstance : (pCore 2 G).Normal) CFSG.pCore_isPGroup hu2
  have hN : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) := by
    intro c hc
    have hcu : Commute c u := Subgroup.mem_centralizer_singleton_iff.mp hc
    exact mem_normalizer_pSpan (fun L hL => SectData.ae8a_conjSub_mem H hcu hL)
      (fun L hL => SectData.ae8a_conjSub_mem H (Commute.inv_left_iff.mpr hcu) hL)
  have h2 := oddCoreImg_le_of_le_normalizer
    (pSpan_le (fun _ hM => hM.2) :
      pSpan (Generic.centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G)) hN
  rw [h1] at h2
  exact oddCore_eq_bot_of_oddCoreImg (le_bot_iff.mp h2)

private theorem ae8b1_not_commutes_self (H : End18.Hyp Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    ¬ Commutes L L := by
  intro hc
  obtain ⟨P₀, ⟨hP₀L, -, hmax⟩, hnc⟩ := (H.endHyp.thmD.hyp.omega1 L hL).2
  have hPL : L = P₀ := hmax L le_rfl (H.endHyp.thmD.two L hL) hP₀L
  subst hPL
  exact hnc (IsMulCommutative.of_comm fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2))

private theorem ae8b1_label_inj (H : End18.Hyp Ω) {m : ℕ}
    (I : AEIdent (Generic.centMembers Ω u) m) (hk : IsPGroup 2 ↥I.φ.ker) :
    ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u,
      (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ =
        (L'.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ → L = L' := by
  intro L hL L' hL' he
  by_contra hne
  set X := pSpan (Generic.centMembers Ω u) with hX
  set Q := (L.subgroupOf X).map I.φ with hQ
  have hQ2 : IsPGroup 2 ↥Q :=
    ((H.endHyp.thmD.two L hL.1).of_equiv (Subgroup.subgroupOfEquivOfLe (le_pSpan hL)).symm).map _
  have hH2 : IsPGroup 2 ↥((Q.comap I.φ).map X.subtype) :=
    (hQ2.comap_of_ker_isPGroup I.φ hk).map _
  have hLH : L ≤ (Q.comap I.φ).map X.subtype := fun l hl =>
    ⟨⟨l, le_pSpan hL hl⟩, I.mem_map hL hl, rfl⟩
  have hL'H : L' ≤ (Q.comap I.φ).map X.subtype := fun l hl =>
    ⟨⟨l, le_pSpan hL' hl⟩, by
      show I.φ ⟨l, le_pSpan hL' hl⟩ ∈ Q
      rw [he]
      exact I.mem_map hL' hl, rfl⟩
  have hc : Commutes L L' :=
    TL4.commutes_of_le_two H.endHyp.thmD.hyp H.endHyp.thmD.two hL.1 hL'.1 hne hH2 hLH hL'H
  refine ae8b1_not_commutes_self H hL.1 fun a ha b hb => ?_
  have hbQ : I.φ ⟨b, le_pSpan hL hb⟩ ∈ (L'.subgroupOf X).map I.φ := by
    rw [← he]
    exact I.mem_map hL hb
  obtain ⟨y, hy, hyb⟩ := hbQ
  have hyL' : (y : G) ∈ L' := Subgroup.mem_subgroupOf.mp hy
  have hk0 : (⟨b, le_pSpan hL hb⟩ : ↥X)⁻¹ * y ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyb, inv_mul_cancel]
  have hcenter := Subgroup.mem_center_iff.mp (I.ker_le hk0) ⟨a, le_pSpan hL ha⟩
  have hak : a * (b⁻¹ * (y : G)) = (b⁻¹ * (y : G)) * a := by
    have := congrArg Subtype.val hcenter
    simpa using this
  have hay : a * (y : G) = (y : G) * a := hc a ha y hyL'
  have key : a * b * (b⁻¹ * (y : G)) = b * a * (b⁻¹ * (y : G)) := by
    calc a * b * (b⁻¹ * (y : G)) = a * (y : G) := by group
      _ = (y : G) * a := hay
      _ = b * (b⁻¹ * (y : G)) * a := by rw [mul_inv_cancel_left]
      _ = b * ((b⁻¹ * (y : G)) * a) := by group
      _ = b * (a * (b⁻¹ * (y : G))) := by rw [hak]
      _ = b * a * (b⁻¹ * (y : G)) := by group
  exact mul_right_cancel key

private theorem ae8b1_five_le (H : End18.Hyp Ω) (hu : SectData Ω u) {m : ℕ}
    (I : AEIdent (Generic.centMembers Ω u) m) (hk : IsPGroup 2 ↥I.φ.ker) : 5 ≤ m := by
  have hinj := ae8b1_label_inj H I hk
  obtain ⟨L₀, hL₀⟩ : (Generic.centMembers Ω u).Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    have h0 : pSpan (Generic.centMembers Ω u) ≤ ⊥ :=
      pSpan_le fun L hL => by simp [hem] at hL
    exact hu.ne_one (Subgroup.mem_bot.mp (h0 hu.mem_span))
  obtain ⟨α, hα, -, -⟩ := I.label L₀ hL₀
  have hm4 : 4 ≤ m := by
    have := Finset.card_le_univ α
    simp only [Fintype.card_fin] at this
    omega
  by_contra hlt
  have hm : m = 4 := by omega
  subst hm
  have hlab : ∀ A ∈ Generic.centMembers Ω u, ∃ b : Bool,
      (A.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ =
        AE.memBar (Finset.univ : Finset (Fin 4)) (by simp) b := by
    intro A hA
    obtain ⟨α', hα', b, hl⟩ := I.label A hA
    have hαu : α' = Finset.univ := Finset.eq_univ_of_card α' (by rw [hα']; simp)
    subst hαu
    exact ⟨b, hl⟩
  obtain ⟨R, hRP, T, hTP, -, hTK⟩ := hu.adj
  have hR : R ∈ Ω := hRP.1
  have hTV : T ∉ twinSet Ω R := by rwa [EndHyp.kPerp_eq_twinSet_of_perp9 H.endHyp H.perp9 hR] at hTK
  have hRself : R ∈ twinSet Ω R := by
    obtain ⟨z, hz⟩ := (H.endHyp.thmD.hyp.omega1 R hR).1
    exact ⟨hR, z, hz, hz⟩
  obtain ⟨x, y, hxy, hS⟩ := Set.ncard_eq_two.mp (hu.ncard_twin H R hRP)
  have hRS : R ∈ twinSet Ω R ∩ Generic.centMembers Ω u := ⟨hRself, hRP⟩
  rw [hS] at hRS
  have hx : x ∈ twinSet Ω R ∩ Generic.centMembers Ω u := by
    rw [hS]; exact Set.mem_insert _ _
  have hy : y ∈ twinSet Ω R ∩ Generic.centMembers Ω u := by
    rw [hS]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨R', hR'S, hR'R⟩ : ∃ R' ∈ twinSet Ω R ∩ Generic.centMembers Ω u, R' ≠ R := by
    rcases Set.mem_insert_iff.mp hRS with h | h
    · exact ⟨y, hy, fun e => hxy (h.symm.trans e.symm)⟩
    · exact ⟨x, hx, fun e => hxy (e.trans (Set.mem_singleton_iff.mp h))⟩
  have hR'P : R' ∈ Generic.centMembers Ω u := hR'S.2
  have hR'tw : R' ∈ twinSet Ω R := hR'S.1
  have hRT : R ≠ T := fun e => hTV (by rw [← e]; exact hRself)
  have hR'T : R' ≠ T := fun e => hTV (by rw [← e]; exact hR'tw)
  obtain ⟨bR, hbR⟩ := hlab R hRP
  obtain ⟨bR', hbR'⟩ := hlab R' hR'P
  obtain ⟨bT, hbT⟩ := hlab T hTP
  cases bR <;> cases bR' <;> cases bT
  all_goals first
    | exact hR'R (hinj R' hR'P R hRP (hbR'.trans hbR.symm))
    | exact hRT (hinj R hRP T hTP (hbR.trans hbT.symm))
    | exact hR'T (hinj R' hR'P T hTP (hbR'.trans hbT.symm))

theorem ae8b1_aeCoverHyp (H : End18.Hyp Ω) (hu : SectData Ω u) {m : ℕ}
    (I : AEIdent (Generic.centMembers Ω u) m) : TL4.AECoverHyp I := by
  have hk : IsPGroup 2 ↥I.φ.ker := I.isPGroup_ker (ae8b1_oddCore H hu)
  have hinj := ae8b1_label_inj H I hk
  have hm5 := ae8b1_five_le H hu I hk
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun _ h => h.1
  have hcomm : ∀ (α : Finset (Fin m)) (h : α.card = 4), ∀ L ∈ Generic.centMembers Ω u,
      ∀ L' ∈ Generic.centMembers Ω u,
      (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ = AE.memBar α h true →
      (L'.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ = AE.memBar α h false →
      ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
    intro α h L hL L' hL' hl hl'
    have hne : L ≠ L' := by
      rintro rfl
      rw [hl] at hl'
      exact AE.memBar_true_ne_false hm5 α h hl'
    refine aeIdent_comm_of_map_comm H.endHyp.thmD.hyp H.endHyp.thmD.two hPΩ I hk hL hL' hne ?_
    rw [hl, hl']
    exact memBar_twin_comm α h true
  exact
    { ker_two := hk
      card := fun L hL => by rw [H.endHyp.thmD.card L hL.1]; norm_num
      conj_mem := fun L hL x hx =>
        SectData.ae8a_conjSub_mem H (Subgroup.mem_centralizer_singleton_iff.mp
          (pSpan_le (fun _ hM => hM.2) hx)) hL
      label_inj := hinj
      twin_comm := hcomm
      twin_z := fun α h L hL L' hL' hl hl' v v' hv hv' =>
        H.perp9 L hL.1 L' hL'.1 (hcomm α h L hL L' hL' hl hl') v v' hv hv' }

private theorem ae8b1_central_absurd (H : End18.Hyp Ω) (hu : SectData Ω u) {m : ℕ} (hm : 5 ≤ m)
    (I : AEIdent (Generic.centMembers Ω u) m) (hker : I.φ.ker = ⊥) : False := by
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff I.φ).mp hker
  have hx1 : I.φ ⟨u, hu.mem_span⟩ ≠ 1 := by
    intro h
    have h1 : (⟨u, hu.mem_span⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 :=
      hinj (h.trans (map_one I.φ).symm)
    exact hu.ne_one (congrArg Subtype.val h1)
  apply hx1
  apply ae8b1_centre_image hm
  intro a ha
  have hrange : AE.mkQ m a ∈ I.φ.range := by
    rw [I.range_eq]
    exact ⟨a, ha, rfl⟩
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hrange
  rw [← hy, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hyC : u * (y : G) = (y : G) * u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun _ hM => hM.2) y.2)).symm
  show u * (y : G) = (y : G) * u
  exact hyC

private theorem ae8b1_even_false (H : End18.Hyp Ω) (hu : SectData Ω u) {m : ℕ}
    (I : AEIdent (Generic.centMembers Ω u) m) (hm8 : 8 ≤ m) : False := by
  have hk : IsPGroup 2 ↥I.φ.ker := I.isPGroup_ker (ae8b1_oddCore H hu)
  have hm5 : 5 ≤ m := by omega
  have hinj := ae8b1_label_inj H I hk
  have hPΩ : Generic.centMembers Ω u ⊆ Ω := fun _ h => h.1
  obtain ⟨R, hRP, -⟩ := hu.adj
  obtain ⟨α, hα, b, hlR⟩ := I.label R hRP
  have hcα : 4 ≤ αᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, hα]
    omega
  obtain ⟨β, hβsub, hβcard⟩ := Finset.exists_subset_card_eq hcα
  have hαβ : Disjoint α β := Finset.disjoint_of_subset_right hβsub disjoint_compl_right
  obtain ⟨L₁, hL₁P, hL₁⟩ := I.label_surj α hα (!b)
  obtain ⟨L₂, hL₂P, hL₂⟩ := I.label_surj β hβcard true
  obtain ⟨L₃, hL₃P, hL₃⟩ := I.label_surj β hβcard false
  have hne_of : ∀ (A B : Subgroup G) {Q₁ Q₂ : Subgroup (AE.AEQ m)},
      (A.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ = Q₁ →
      (B.subgroupOf (pSpan (Generic.centMembers Ω u))).map I.φ = Q₂ → Q₁ ≠ Q₂ → A ≠ B := by
    intro A B Q₁ Q₂ hA hB hQ e
    subst e
    exact hQ (hA.symm.trans hB)
  have hαne : ∀ c d : Bool, AE.memBar α hα c ≠ AE.memBar β hβcard d := by
    intro c d e
    have hαβeq := AE.eq_of_memBar_eq' hm5 e
    rw [← hαβeq] at hαβ
    have h0 := (Finset.disjoint_self_iff_empty α).mp hαβ
    rw [h0, Finset.card_empty] at hα
    exact absurd hα (by norm_num)
  have hbb : AE.memBar α hα b ≠ AE.memBar α hα (!b) := by
    cases b
    · exact fun e => AE.memBar_true_ne_false hm5 α hα e.symm
    · exact AE.memBar_true_ne_false hm5 α hα
  have hRL₁ : R ≠ L₁ := hne_of R L₁ hlR hL₁ hbb
  have hRL₂ : R ≠ L₂ := hne_of R L₂ hlR hL₂ (hαne b true)
  have hRL₃ : R ≠ L₃ := hne_of R L₃ hlR hL₃ (hαne b false)
  have hL₁L₂ : L₁ ≠ L₂ := hne_of L₁ L₂ hL₁ hL₂ (hαne (!b) true)
  have hcR₁ : Commutes R L₁ :=
    aeIdent_comm_of_map_comm H.endHyp.thmD.hyp H.endHyp.thmD.two hPΩ I hk hRP hL₁P hRL₁
      (by rw [hlR, hL₁]; exact memBar_twin_comm α hα b)
  have hcR₂ : Commutes R L₂ :=
    aeIdent_comm_of_map_comm H.endHyp.thmD.hyp H.endHyp.thmD.two hPΩ I hk hRP hL₂P hRL₂
      (by rw [hlR, hL₂]; exact AE.comm_memBar_of_disjoint hαβ b true)
  have hcR₃ : Commutes R L₃ :=
    aeIdent_comm_of_map_comm H.endHyp.thmD.hyp H.endHyp.thmD.two hPΩ I hk hRP hL₃P hRL₃
      (by rw [hlR, hL₃]; exact AE.comm_memBar_of_disjoint hαβ b false)
  have hT₁ : L₁ ∈ twinSet Ω R := ae8b1_twin_of_comm H hRP.1 hL₁P.1 hcR₁
  have hT₂ : L₂ ∈ twinSet Ω R := ae8b1_twin_of_comm H hRP.1 hL₂P.1 hcR₂
  have hRself : R ∈ twinSet Ω R := by
    obtain ⟨z, hz⟩ := (H.endHyp.thmD.hyp.omega1 R hRP.1).1
    exact ⟨hRP.1, z, hz, hz⟩
  obtain ⟨x, y, hxy, hS⟩ := Set.ncard_eq_two.mp (hu.ncard_twin H R hRP)
  have mem2 : ∀ A : Subgroup G, A ∈ twinSet Ω R ∩ Generic.centMembers Ω u → A = x ∨ A = y := by
    intro A hA
    rw [hS] at hA
    rcases Set.mem_insert_iff.mp hA with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  have h1 := mem2 R ⟨hRself, hRP⟩
  have h2 := mem2 L₁ ⟨hT₁, hL₁P⟩
  have h3 := mem2 L₂ ⟨hT₂, hL₂P⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first
    | exact hRL₁ (h1.trans h2.symm)
    | exact hRL₂ (h1.trans h3.symm)
    | exact hL₁L₂ (h2.trans h3.symm)

theorem aeIdent_deg_eq_six (H : End18.Hyp Ω) (hu : SectData Ω u) {m : ℕ} (hm : 5 ≤ m)
    (I : AEIdent (Generic.centMembers Ω u) m) : m = 6 := by
  by_contra hne
  rcases Nat.even_or_odd m with hev | hodd
  · obtain ⟨k, hk⟩ := hev
    exact (ae8b1_even_false H hu I (by omega)).elim
  · have hker := TL4.aeCoverOddKer_proved G (Generic.centMembers Ω u) m I hm hodd
      (ae8b1_aeCoverHyp H hu I)
    exact (ae8b1_central_absurd H hu hm I hker).elim

theorem aeCoverHyp_of_aeIdent (H : End18.Hyp Ω) (hu : SectData Ω u) {m : ℕ}
    (I : AEIdent (Generic.centMembers Ω u) m) : TL4.AECoverHyp I :=
  ae8b1_aeCoverHyp H hu I

theorem exists_aeCover_six (H : End18.Hyp Ω) (hu : SectData Ω u) :
    ∃ I : AEIdent (Generic.centMembers Ω u) 6, TL4.AECoverHyp I := by
  obtain ⟨m, hm, ⟨I⟩⟩ := hu.exists_aeIdent H
  have h6 : m = 6 := aeIdent_deg_eq_six H hu hm I
  subst h6
  exact ⟨I, aeCoverHyp_of_aeIdent H hu I⟩

structure Chart (Ω : Set (Subgroup G)) (u : G) where
  mem : u ∈ pSpan (Generic.centMembers Ω u)
  ψ : ↥(pSpan (Generic.centMembers Ω u)) ≃* ↥(AE.aeSub 6)
  label : ∀ L ∈ Generic.centMembers Ω u,
    ∃ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
      ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map ψ.toMonoidHom).map
        (AE.aeSub 6).subtype = AE.memAt α h b
  label_surj : ∀ (α : Finset (Fin 6)) (h : α.card = 4) (b : Bool),
    ∃ L ∈ Generic.centMembers Ω u,
      ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map ψ.toMonoidHom).map
        (AE.aeSub 6).subtype = AE.memAt α h b
  label_inj : ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u,
    ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map ψ.toMonoidHom).map
        (AE.aeSub 6).subtype =
      ((L'.subgroupOf (pSpan (Generic.centMembers Ω u))).map ψ.toMonoidHom).map
        (AE.aeSub 6).subtype → L = L'
  u_eq : (ψ ⟨u, mem⟩ : AE.Wr 6) = AE.Wr.allOnes 6

theorem exists_chart (H : End18.Hyp Ω) (hu : SectData Ω u) : Nonempty (Chart Ω u) := by
  obtain ⟨I, hAEC⟩ := exists_aeCover_six H hu
  obtain ⟨-, hker⟩ := aeCover_ker hAEC (by norm_num : 5 ≤ 6)
  rcases hker with hbot | ⟨ψ, hψ, hlab⟩
  · exact (ae8b1_central_absurd H hu (by norm_num) I hbot).elim
  · have htr : ∀ S : Subgroup ↥(pSpan (Generic.centMembers Ω u)),
        ((S.map ψ.toMonoidHom).map (AE.aeSub 6).subtype).map (AE.mkQ 6) = S.map I.φ := by
      intro S
      have hcomp : ((AE.mkQ 6).comp (AE.aeSub 6).subtype).comp ψ.toMonoidHom = I.φ :=
        MonoidHom.ext fun x => hψ x
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    refine ⟨{ mem := hu.mem_span
              ψ := ψ
              label := fun L hL => ?_
              label_surj := fun α h b => ?_
              label_inj := fun L hL L' hL' he => ?_
              u_eq := ?_ }⟩
    · obtain ⟨α, h, b, hl⟩ := I.label L hL
      exact ⟨α, h, b, hlab L hL α h b hl⟩
    · obtain ⟨L, hL, hl⟩ := I.label_surj α h b
      exact ⟨L, hL, hlab L hL α h b hl⟩
    · apply hAEC.label_inj L hL L' hL'
      rw [← htr, ← htr, he]
    · have hwc : ∀ a ∈ AE.aeSub 6,
          ((ψ ⟨u, hu.mem_span⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) * a =
            a * ((ψ ⟨u, hu.mem_span⟩ : ↥(AE.aeSub 6)) : AE.Wr 6) := by
        intro a ha
        obtain ⟨y, hy⟩ : ∃ y : ↥(pSpan (Generic.centMembers Ω u)), ψ y = ⟨a, ha⟩ :=
          ⟨ψ.symm ⟨a, ha⟩, ψ.apply_symm_apply _⟩
        have hyC : u * (y : G) = (y : G) * u :=
          (Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun _ hM => hM.2) y.2)).symm
        have hcom : (⟨u, hu.mem_span⟩ : ↥(pSpan (Generic.centMembers Ω u))) * y =
            y * ⟨u, hu.mem_span⟩ := Subtype.ext hyC
        have h2 := congrArg ψ hcom
        rw [map_mul, map_mul, hy] at h2
        exact congrArg Subtype.val h2
      rcases ae8b1_centre_aeSub (by norm_num) _ hwc with h | h
      · exfalso
        have h1 : ψ ⟨u, hu.mem_span⟩ = 1 := Subtype.ext h
        have h2 : (⟨u, hu.mem_span⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 :=
          ψ.injective (h1.trans (map_one ψ).symm)
        exact hu.ne_one (congrArg Subtype.val h2)
      · exact h

namespace Chart

variable (c : Chart Ω u)

theorem ncard_centMembers_of_chart (c : Chart Ω u) : (Generic.centMembers Ω u).ncard = 30 := by
  classical
  choose! α hα b hl using c.label
  have hcongr : ∀ (s s' : Finset (Fin 6)) (h : s.card = 4) (h' : s'.card = 4) (t t' : Bool),
      s = s' → t = t' → AE.memAt s h t = AE.memAt s' h' t' := by
    rintro s s' h h' t t' rfl rfl
    rfl
  have key : (Generic.centMembers Ω u).ncard =
      ({p : Finset (Fin 6) × Bool | p.1.card = 4} : Set (Finset (Fin 6) × Bool)).ncard := by
    refine Set.ncard_congr (fun L _ => (α L, b L)) (fun L hL => hα L hL) ?_ ?_
    · intro L L' hL hL' he
      obtain ⟨e1, e2⟩ := Prod.mk.inj he
      apply c.label_inj L hL L' hL'
      rw [hl L hL, hl L' hL']
      exact hcongr _ _ _ _ _ _ e1 e2
    · rintro ⟨s, t⟩ hst
      have hs : s.card = 4 := hst
      obtain ⟨L, hL, hLl⟩ := c.label_surj s hs t
      refine ⟨L, hL, ?_⟩
      obtain ⟨e1, e2⟩ := ae8b1_memAt_inj (by norm_num) ((hl L hL).symm.trans hLl)
      exact Prod.ext e1 e2
  rw [key]
  have hset : ({p : Finset (Fin 6) × Bool | p.1.card = 4} : Set (Finset (Fin 6) × Bool)) =
      ↑(Finset.univ.filter (fun p : Finset (Fin 6) × Bool => p.1.card = 4)) := by
    ext p
    simp
  have hfilt : Finset.univ.filter (fun p : Finset (Fin 6) × Bool => p.1.card = 4) =
      Finset.univ.powersetCard 4 ×ˢ Finset.univ := by
    ext ⟨s, t⟩
    simp [Finset.mem_powersetCard]
  rw [hset, Set.ncard_coe_finset, hfilt, Finset.card_product, Finset.card_powersetCard]
  simp
  rfl

include c in
theorem ncard_centMembers : (Generic.centMembers Ω u).ncard = 30 :=
  ncard_centMembers_of_chart c

section Ae8b2Aux

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Equiv

@[expose] def ae8b2_ind (s : Finset (Fin 6)) : Fin 6 → ZMod 2 := fun x => if x ∈ s then 1 else 0

theorem ae8b2_ofVec_mul (x y : Fin 6 → ZMod 2) : ofVec x * ofVec y = ofVec (x + y) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rfl
  · rfl

theorem ae8b2_ofVec_inv (x : Fin 6 → ZMod 2) : (ofVec x)⁻¹ = ofVec x := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rfl
  · rfl

theorem ae8b2_conj_ofPerm (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    ofPerm σ * ofVec x * (ofPerm σ)⁻¹ = ofVec (fun i => x (σ.symm i)) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · simp [mul_vec, inv_vec, ofPerm, ofVec, mul_perm, inv_perm]
  · simp [mul_perm, inv_perm, ofPerm, ofVec]

theorem ae8b2_piSub_ofVec (f : Fin 6 → ZMod 2) : ofVec f ∈ piSub 6 ↔ f = 0 ∨ f = 1 := by
  constructor
  · rintro (h | h)
    · left
      exact congrArg Wr.vec h
    · right
      exact congrArg Wr.vec h
  · rintro (h | h)
    · left
      refine Wr.ext (funext fun i => ?_) ?_
      · exact congrFun h i
      · rfl
    · right
      refine Wr.ext (funext fun i => ?_) ?_
      · exact congrFun h i
      · rfl

theorem ae8b2_mkQ_comm_iff (a b : Wr 6) :
    mkQ 6 a * mkQ 6 b = mkQ 6 b * mkQ 6 a ↔ a * b * a⁻¹ * b⁻¹ ∈ piSub 6 := by
  have e : a * b * a⁻¹ * b⁻¹ ∈ piSub 6 ↔ mkQ 6 (a * b * a⁻¹ * b⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).symm
  have h : mkQ 6 (a * b * a⁻¹ * b⁻¹) = mkQ 6 a * mkQ 6 b * (mkQ 6 a)⁻¹ * (mkQ 6 b)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [e, h]
  constructor
  · intro hc
    rw [hc]
    group
  · intro hc
    calc mkQ 6 a * mkQ 6 b = (mkQ 6 a * mkQ 6 b * (mkQ 6 a)⁻¹ * (mkQ 6 b)⁻¹) *
          (mkQ 6 b * mkQ 6 a) := by group
      _ = mkQ 6 b * mkQ 6 a := by rw [hc, one_mul]

theorem ae8b2_zmod2_pair (p a b : ZMod 2) : p + a + p + b = a + b := by
  have h := zmod_two_add_self p
  calc p + a + p + b = (p + p) + a + b := by abel
    _ = a + b := by rw [h, zero_add]

theorem ae8b2_wr_eq (v : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) :
    (⟨v, σ⟩ : Wr 6) = ofVec v * ofPerm σ := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show v i = v i + 0
    simp
  · show σ = 1 * σ
    simp

theorem ae8b2_comm_vec_conj (v x : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) :
    (⟨v, σ⟩ : Wr 6) * ofVec x * (⟨v, σ⟩ : Wr 6)⁻¹ * (ofVec x)⁻¹ =
      ofVec (fun i => x (σ.symm i) + x i) := by
  rw [ae8b2_wr_eq, mul_inv_rev, ae8b2_ofVec_inv, ae8b2_ofVec_inv]
  have e : ofVec v * ofPerm σ * ofVec x * ((ofPerm σ)⁻¹ * ofVec v) * ofVec x =
      ofVec v * (ofPerm σ * ofVec x * (ofPerm σ)⁻¹) * ofVec v * ofVec x := by group
  rw [e, ae8b2_conj_ofPerm, ae8b2_ofVec_mul, ae8b2_ofVec_mul, ae8b2_ofVec_mul]
  congr 1
  funext i
  exact ae8b2_zmod2_pair _ _ _

theorem ae8b2_comm_vec_iff (w : Wr 6) (x : Fin 6 → ZMod 2) :
    mkQ 6 w * mkQ 6 (ofVec x) = mkQ 6 (ofVec x) * mkQ 6 w ↔
      (fun i => x (w.perm.symm i)) = x ∨ (fun i => x (w.perm.symm i)) = x + 1 := by
  rw [ae8b2_mkQ_comm_iff]
  rcases w with ⟨v, σ⟩
  rw [ae8b2_comm_vec_conj, ae8b2_piSub_ofVec]
  have k0 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  have k1 : ∀ a b : ZMod 2, a + b = 1 ↔ a = b + 1 := by decide
  constructor
  · rintro (h | h)
    · left
      funext i
      exact (k0 _ _).mp (congrFun h i)
    · right
      funext i
      exact (k1 _ _).mp (congrFun h i)
  · rintro (h | h)
    · left
      funext i
      exact (k0 _ _).mpr (congrFun h i)
    · right
      funext i
      exact (k1 _ _).mpr (congrFun h i)

theorem ae8b2_ite_zmod_iff (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ZMod 2) else 0) = (if q then 1 else 0) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> (try decide)

theorem ae8b2_ite_zmod_add_one (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ZMod 2) else 0) = (if q then 1 else 0) + 1 ↔ (p ↔ ¬ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> (try decide)

theorem ae8b2_not_complement (σ : Equiv.Perm (Fin 6)) (S : Finset (Fin 6))
    (hS : ∑ j, (if j ∈ S then (1:ℕ) else 0) = 2)
    (h : ∀ j, (if σ.symm j ∈ S then (1:ℕ) else 0) + (if j ∈ S then 1 else 0) = 1) : False := by
  have h1 : ∑ j, (if σ.symm j ∈ S then (1:ℕ) else 0) = ∑ j, (if j ∈ S then (1:ℕ) else 0) :=
    Equiv.sum_comp σ.symm (fun j => if j ∈ S then (1:ℕ) else 0)
  have h2 : ∑ j, ((if σ.symm j ∈ S then (1:ℕ) else 0) + (if j ∈ S then 1 else 0)) =
      ∑ _j : Fin 6, (1:ℕ) := Finset.sum_congr rfl (fun j _ => h j)
  rw [Finset.sum_add_distrib, h1, hS] at h2
  simp at h2

theorem ae8b2_card_pair_sum : ∀ i : Fin 6, i ≠ 0 →
    ∑ j, (if j ∈ ({0, i} : Finset (Fin 6)) then (1:ℕ) else 0) = 2 := by decide

theorem ae8b2_pair_fix_iff : ∀ j k : Fin 6, (∀ i : Fin 6, i ≠ 0 →
    (k ∈ ({0, i} : Finset (Fin 6)) ↔ j ∈ ({0, i} : Finset (Fin 6)))) → j = k := by decide

theorem ae8b2_perm_one_of_pairs (σ : Equiv.Perm (Fin 6))
    (h : ∀ i : Fin 6, i ≠ 0 → ((fun j => ae8b2_ind {0, i} (σ.symm j)) = ae8b2_ind {0, i} ∨
      (fun j => ae8b2_ind {0, i} (σ.symm j)) = ae8b2_ind {0, i} + 1)) : σ = 1 := by
  have hfix : ∀ i : Fin 6, i ≠ 0 → ∀ j : Fin 6,
      (σ.symm j ∈ ({0, i} : Finset (Fin 6)) ↔ j ∈ ({0, i} : Finset (Fin 6))) := by
    intro i hi j
    rcases h i hi with h1 | h1
    · have hj := congrFun h1 j
      simp only [ae8b2_ind] at hj
      exact (ae8b2_ite_zmod_iff _ _).mp hj
    · exfalso
      have hj : ∀ j, (if σ.symm j ∈ ({0, i} : Finset (Fin 6)) then (1:ℕ) else 0) +
          (if j ∈ ({0, i} : Finset (Fin 6)) then 1 else 0) = 1 := by
        intro j
        have hj := congrFun h1 j
        simp only [ae8b2_ind, Pi.add_apply] at hj
        exact (by
          have := (ae8b2_ite_zmod_add_one _ _).mp hj
          by_cases hp : σ.symm j ∈ ({0, i} : Finset (Fin 6)) <;>
            by_cases hq : j ∈ ({0, i} : Finset (Fin 6)) <;> simp_all)
      exact ae8b2_not_complement σ _ (ae8b2_card_pair_sum i hi) hj |>.elim
  have hsymm : ∀ j : Fin 6, σ.symm j = j := by
    intro j
    have := ae8b2_pair_fix_iff j (σ.symm j) (fun i hi => hfix i hi j)
    exact this.symm
  apply Equiv.ext
  intro j
  show σ j = j
  have h2 : σ.symm (σ j) = σ j := hsymm (σ j)
  rw [Equiv.symm_apply_apply] at h2
  exact h2.symm

theorem ae8b2_comm_ofPerm_ofVec (x : Fin 6 → ZMod 2) (σ : Equiv.Perm (Fin 6)) :
    ofVec x * ofPerm σ * (ofVec x)⁻¹ * (ofPerm σ)⁻¹ = ofVec (x + fun i => x (σ.symm i)) := by
  rw [ae8b2_ofVec_inv]
  have e : ofVec x * ofPerm σ * ofVec x * (ofPerm σ)⁻¹ =
      ofVec x * (ofPerm σ * ofVec x * (ofPerm σ)⁻¹) := by group
  rw [e, ae8b2_conj_ofPerm, ae8b2_ofVec_mul]

theorem ae8b2_wsum_ofVec (x : Fin 6 → ZMod 2) : ofVec x ∈ aeSub 6 ↔ ∑ j, x j = 0 := by
  rw [mem_aeSub]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, by simp [ofVec]⟩

theorem ae8b2_ofPerm_mem (σ : Equiv.Perm (Fin 6)) (hσ : Equiv.Perm.sign σ = 1) :
    ofPerm σ ∈ aeSub 6 := by
  rw [mem_aeSub]
  exact ⟨by simp [ofPerm, wsum], hσ⟩

theorem ae8b2_vec_of_comm_pairs (z : AEQ 6)
    (hz : ∀ i : Fin 6, i ≠ 0 →
      mkQ 6 (ofVec (ae8b2_ind {0, i})) * z = z * mkQ 6 (ofVec (ae8b2_ind {0, i}))) :
    ∃ v : Fin 6 → ZMod 2, z = mkQ 6 (ofVec v) := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective z
  have hwz : mkQ 6 w = z := hw
  subst hwz
  have hperm : w.perm = 1 :=
    ae8b2_perm_one_of_pairs w.perm (fun i hi => (ae8b2_comm_vec_iff w _).mp (hz i hi).symm)
  refine ⟨w.vec, ?_⟩
  congr 1
  exact Wr.ext rfl hperm

theorem ae8b2_three_cycle_const (v : Fin 6 → ZMod 2) (τ : Equiv.Perm (Fin 6)) (j0 : Fin 6)
    (hj0 : τ.symm j0 = j0)
    (h : (v + fun i => v (τ.symm i)) = 0 ∨ (v + fun i => v (τ.symm i)) = 1) :
    ∀ j, v (τ.symm j) = v j := by
  have k0 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  rcases h with h | h
  · intro j
    have hj := congrFun h j
    simp only [Pi.add_apply, Pi.zero_apply] at hj
    exact ((k0 _ _).mp hj).symm
  · exfalso
    have hj := congrFun h j0
    simp only [Pi.add_apply, Pi.one_apply, hj0] at hj
    rw [zmod_two_add_self] at hj
    exact absurd hj (by decide)

theorem ae8b2_cent_trivial (z : AEQ 6)
    (hz : ∀ g ∈ (aeSub 6).map (mkQ 6), z * g = g * z) : z = 1 := by
  have hpair : ∀ i : Fin 6, i ≠ 0 →
      mkQ 6 (ofVec (ae8b2_ind {0, i})) * z = z * mkQ 6 (ofVec (ae8b2_ind {0, i})) := by
    intro i hi
    have hsum : ∀ i : Fin 6, i ≠ 0 → ∑ j, ae8b2_ind {0, i} j = 0 := by decide
    have hmem : ofVec (ae8b2_ind {0, i}) ∈ aeSub 6 := (ae8b2_wsum_ofVec _).mpr (hsum i hi)
    exact (hz _ (Subgroup.mem_map_of_mem _ hmem)).symm
  obtain ⟨v, rfl⟩ := ae8b2_vec_of_comm_pairs z hpair
  have hcomm : ∀ τ : Equiv.Perm (Fin 6), Equiv.Perm.sign τ = 1 → ∀ j0 : Fin 6, τ.symm j0 = j0 →
      ∀ j, v (τ.symm j) = v j := by
    intro τ hτ j0 hj0
    have hm : mkQ 6 (ofPerm τ) ∈ (aeSub 6).map (mkQ 6) :=
      Subgroup.mem_map_of_mem _ (ae8b2_ofPerm_mem τ hτ)
    have h1 := (ae8b2_mkQ_comm_iff (ofVec v) (ofPerm τ)).mp (hz _ hm)
    rw [ae8b2_comm_ofPerm_ofVec, ae8b2_piSub_ofVec] at h1
    exact ae8b2_three_cycle_const v τ j0 hj0 h1
  have hA := hcomm (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2) (by decide) 3 (by decide)
  have hB := hcomm (Equiv.swap (0 : Fin 6) 3 * Equiv.swap (3 : Fin 6) 4) (by decide) 1 (by decide)
  have hC := hcomm (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 5) (by decide) 2 (by decide)
  have e2 : v 2 = v 0 := by
    have := hA 0
    rwa [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2).symm (0 : Fin 6) = (2 : Fin 6)
      from by decide] at this
  have e1 : v 1 = v 0 := by
    have := hA 1
    rw [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2).symm (1 : Fin 6) = (0 : Fin 6)
      from by decide] at this
    exact this.symm
  have e4 : v 4 = v 0 := by
    have := hB 0
    rwa [show (Equiv.swap (0 : Fin 6) 3 * Equiv.swap (3 : Fin 6) 4).symm (0 : Fin 6) = (4 : Fin 6)
      from by decide] at this
  have e3 : v 3 = v 0 := by
    have := hB 3
    rw [show (Equiv.swap (0 : Fin 6) 3 * Equiv.swap (3 : Fin 6) 4).symm (3 : Fin 6) = (0 : Fin 6)
      from by decide] at this
    exact this.symm
  have e5 : v 5 = v 0 := by
    have := hC 0
    rwa [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 5).symm (0 : Fin 6) = (5 : Fin 6)
      from by decide] at this
  have hall : ∀ j : Fin 6, v j = v 0 := by
    intro j
    fin_cases j
    · rfl
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hmem : ofVec v ∈ piSub 6 := by
    rw [ae8b2_piSub_ofVec]
    rcases hc (v 0) with h0 | h0
    · left
      funext j
      rw [hall j, h0]
      rfl
    · right
      funext j
      rw [hall j, h0]
      rfl
  exact (QuotientGroup.eq_one_iff _).mpr hmem

theorem ae8b2_comm_mem_CA (a b : Wr 6) (ha : a ∈ aeSub 6) (hb : b ∈ aeSub 6) :
    a * b * a⁻¹ * b⁻¹ ∈ (commutator (↥(aeSub 6))).map (aeSub 6).subtype := by
  refine Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : ↥(aeSub 6)) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥(aeSub 6))⁻¹ *
    (⟨b, hb⟩ : ↥(aeSub 6))⁻¹, ?_, rfl⟩
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem ae8b2_pair_mem (i : Fin 6) (hi : i ≠ 0) :
    ofVec (ae8b2_ind {0, i}) ∈ (commutator (↥(aeSub 6))).map (aeSub 6).subtype := by
  have hA : ofVec (ae8b2_ind {0, 4}) ∈ aeSub 6 := (ae8b2_wsum_ofVec _).mpr (by decide)
  fin_cases i
  · exact absurd rfl hi
  · have h := ae8b2_comm_mem_CA (ofVec (ae8b2_ind {0, 4}))
      (ofPerm (Equiv.swap (0 : Fin 6) 1 * Equiv.swap (2 : Fin 6) 3))
      hA (ae8b2_ofPerm_mem _ (by decide))
    rw [ae8b2_comm_ofPerm_ofVec] at h
    convert h using 2
    decide
  · have h := ae8b2_comm_mem_CA (ofVec (ae8b2_ind {0, 4}))
      (ofPerm (Equiv.swap (0 : Fin 6) 2 * Equiv.swap (1 : Fin 6) 3))
      hA (ae8b2_ofPerm_mem _ (by decide))
    rw [ae8b2_comm_ofPerm_ofVec] at h
    convert h using 2
    decide
  · have h := ae8b2_comm_mem_CA (ofVec (ae8b2_ind {0, 4}))
      (ofPerm (Equiv.swap (0 : Fin 6) 3 * Equiv.swap (1 : Fin 6) 2))
      hA (ae8b2_ofPerm_mem _ (by decide))
    rw [ae8b2_comm_ofPerm_ofVec] at h
    convert h using 2
    decide
  · have hB : ofVec (ae8b2_ind {0, 3}) ∈ aeSub 6 := (ae8b2_wsum_ofVec _).mpr (by decide)
    have h := ae8b2_comm_mem_CA (ofVec (ae8b2_ind {0, 3}))
      (ofPerm (Equiv.swap (0 : Fin 6) 4 * Equiv.swap (1 : Fin 6) 2))
      hB (ae8b2_ofPerm_mem _ (by decide))
    rw [ae8b2_comm_ofPerm_ofVec] at h
    convert h using 2
    decide
  · have hB : ofVec (ae8b2_ind {0, 3}) ∈ aeSub 6 := (ae8b2_wsum_ofVec _).mpr (by decide)
    have h := ae8b2_comm_mem_CA (ofVec (ae8b2_ind {0, 3}))
      (ofPerm (Equiv.swap (0 : Fin 6) 5 * Equiv.swap (1 : Fin 6) 2))
      hB (ae8b2_ofPerm_mem _ (by decide))
    rw [ae8b2_comm_ofPerm_ofVec] at h
    convert h using 2
    decide

theorem ae8b2_zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem ae8b2_vec_mem_CA (v : Fin 6 → ZMod 2) (hv : ∑ j, v j = 0) :
    ofVec v ∈ (commutator (↥(aeSub 6))).map (aeSub 6).subtype := by
  have hv' : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 = 0 := by simpa [Fin.sum_univ_six] using hv
  have hdec : v = ∑ i : Fin 5, v i.succ • ae8b2_ind {0, i.succ} := by
    funext j
    fin_cases j <;> simp [Fin.sum_univ_five, ae8b2_ind] <;> revert hv' <;> generalize v 0 = a <;>
      generalize v 1 = b <;> generalize v 2 = c <;> generalize v 3 = d <;>
      generalize v 4 = e <;> generalize v 5 = f <;> revert a b c d e f <;> decide
  have hc := ae8b2_zmod2_cases
  rw [hdec]
  refine Finset.sum_induction _ (fun w => ofVec w ∈ (commutator (↥(aeSub 6))).map (aeSub 6).subtype)
    (fun a b ha hb => ?_) ?_ (fun i _ => ?_)
  · rw [← ae8b2_ofVec_mul]
    exact Subgroup.mul_mem _ ha hb
  · exact Subgroup.one_mem _
  · rcases hc (v i.succ) with h0 | h0
    · have e : v i.succ • ae8b2_ind {0, i.succ} = 0 := by
        rw [h0]
        funext j
        simp
      rw [e]
      exact Subgroup.one_mem _
    · have e : v i.succ • ae8b2_ind {0, i.succ} = ae8b2_ind {0, i.succ} := by
        rw [h0]
        funext j
        simp
      rw [e]
      exact ae8b2_pair_mem _ (Fin.succ_ne_zero i)

theorem ae8b2_aeSub_comm_top : commutator (↥(aeSub 6)) = ⊤ := by
  have hsign : ∀ g : ↥(aeSub 6), Equiv.Perm.sign (g : Wr 6).perm = 1 :=
    fun g => (mem_aeSub.mp g.2).2
  let f : ↥(aeSub 6) →* Equiv.Perm (Fin 6) :=
    { toFun := fun g => (g : Wr 6).perm, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ρ : ↥(aeSub 6) →* alternatingGroup (Fin 6) :=
    f.codRestrict (alternatingGroup (Fin 6))
      (fun g => Equiv.Perm.mem_alternatingGroup.mpr (hsign g))
  have hρ : Function.Surjective ρ := by
    intro τ
    refine ⟨⟨ofPerm (τ : Equiv.Perm (Fin 6)),
      ae8b2_ofPerm_mem _ (Equiv.Perm.mem_alternatingGroup.mp τ.2)⟩, Subtype.ext rfl⟩
  have htop : (⊤ : Subgroup ↥(aeSub 6)).map ρ = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hρ
  have hA : commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hmap : (commutator ↥(aeSub 6)).map ρ = ⊤ := by
    rw [← hA]
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥(aeSub 6)) (⊤ : Subgroup ↥(aeSub 6)) ρ
    rw [htop] at h
    exact h
  rw [eq_top_iff]
  intro g _
  have hg : ρ g ∈ (commutator ↥(aeSub 6)).map ρ := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hρh⟩ := Subgroup.mem_map.mp hg
  have hkρ : ρ (h⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hρh, inv_mul_cancel]
  have hkperm : ((h⁻¹ * g : ↥(aeSub 6)) : Wr 6).perm = 1 := by
    have := congrArg Subtype.val hkρ
    exact this
  have hkvec : ((h⁻¹ * g : ↥(aeSub 6)) : Wr 6) = ofVec ((h⁻¹ * g : ↥(aeSub 6)) : Wr 6).vec :=
    Wr.ext rfl hkperm
  have hsum : ∑ j, ((h⁻¹ * g : ↥(aeSub 6)) : Wr 6).vec j = 0 :=
    (mem_aeSub.mp (h⁻¹ * g : ↥(aeSub 6)).2).1
  obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.mp (ae8b2_vec_mem_CA _ hsum)
  have hkc : c = h⁻¹ * g := Subtype.ext (hck.trans hkvec.symm)
  have hgk : g = h * (h⁻¹ * g) := by group
  rw [hgk, ← hkc]
  exact Subgroup.mul_mem _ hh hc

theorem ae8b2_vec_mem_of_pairs (H : Subgroup (Wr 6))
    (hpair : ∀ i : Fin 6, i ≠ 0 → ofVec (ae8b2_ind {0, i}) ∈ H)
    (v : Fin 6 → ZMod 2) (hv : ∑ j, v j = 0) : ofVec v ∈ H := by
  have hv' : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 = 0 := by simpa [Fin.sum_univ_six] using hv
  have hdec : v = ∑ i : Fin 5, v i.succ • ae8b2_ind {0, i.succ} := by
    funext j
    fin_cases j <;> simp [Fin.sum_univ_five, ae8b2_ind] <;> revert hv' <;> generalize v 0 = a <;>
      generalize v 1 = b <;> generalize v 2 = c <;> generalize v 3 = d <;>
      generalize v 4 = e <;> generalize v 5 = f <;> revert a b c d e f <;> decide
  have hc := ae8b2_zmod2_cases
  rw [hdec]
  refine Finset.sum_induction _ (fun w => ofVec w ∈ H)
    (fun a b ha hb => ?_) ?_ (fun i _ => ?_)
  · rw [← ae8b2_ofVec_mul]
    exact Subgroup.mul_mem _ ha hb
  · exact Subgroup.one_mem _
  · rcases hc (v i.succ) with h0 | h0
    · have e : v i.succ • ae8b2_ind {0, i.succ} = 0 := by
        rw [h0]
        funext j
        simp
      rw [e]
      exact Subgroup.one_mem _
    · have e : v i.succ • ae8b2_ind {0, i.succ} = ae8b2_ind {0, i.succ} := by
        rw [h0]
        funext j
        simp
      rw [e]
      exact hpair _ (Fin.succ_ne_zero i)

theorem ae8b2_perm_one_of_normal (N : Subgroup ↥(aeSub 6)) [N.Normal]
    (hsq : ∀ n ∈ N, n * n = 1) : ∀ n ∈ N, (n : Wr 6).perm = 1 := by
  have hsign : ∀ g : ↥(aeSub 6), Equiv.Perm.sign (g : Wr 6).perm = 1 :=
    fun g => (mem_aeSub.mp g.2).2
  let f : ↥(aeSub 6) →* Equiv.Perm (Fin 6) :=
    { toFun := fun g => (g : Wr 6).perm, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ρ : ↥(aeSub 6) →* alternatingGroup (Fin 6) :=
    f.codRestrict (alternatingGroup (Fin 6))
      (fun g => Equiv.Perm.mem_alternatingGroup.mpr (hsign g))
  have hρ : Function.Surjective ρ := by
    intro τ
    refine ⟨⟨ofPerm (τ : Equiv.Perm (Fin 6)),
      ae8b2_ofPerm_mem _ (Equiv.Perm.mem_alternatingGroup.mp τ.2)⟩, Subtype.ext rfl⟩
  haveI : (N.map ρ).Normal := Subgroup.Normal.map ‹N.Normal› ρ hρ
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 6) (by simp)
      (N := N.map ρ) with h | h
  · intro n hn
    have hmem : ρ n ∈ N.map ρ := Subgroup.mem_map_of_mem _ hn
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    let c : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap (1 : Fin 6) 2,
        Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    have hc : c ∈ N.map ρ := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hρn⟩ := Subgroup.mem_map.mp hc
    have h2 : ρ (n * n) = c * c := by rw [map_mul, hρn]
    rw [hsq n hn, map_one] at h2
    have h3 : ((c * c : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = 1 := by
      rw [← h2]
      rfl
    revert h3
    decide

theorem ae8b2_normalize (v : Fin 6 → ZMod 2) :
    ∃ v' : Fin 6 → ZMod 2, v' 0 = 0 ∧ mkQ 6 (ofVec v') = mkQ 6 (ofVec v) := by
  by_cases h0 : v 0 = 0
  · exact ⟨v, h0, rfl⟩
  · refine ⟨v + fun _ => 1, ?_, ?_⟩
    · have hc : ∀ c : ZMod 2, c ≠ 0 → c + 1 = 0 := by decide
      exact hc _ h0
    · have key : ofVec (v + fun _ => 1) = ofVec v * allOnes 6 := by
        rw [← ae8b2_ofVec_mul]
        rfl
      have hpi : mkQ 6 (allOnes 6) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ((mem_piSub).mpr (Or.inr rfl))
      rw [key, map_mul, hpi, mul_one]

theorem ae8b2_u_central (c : Chart Ω u) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    y * ⟨u, c.mem⟩ = ⟨u, c.mem⟩ * y := by
  have hle : pSpan (Generic.centMembers Ω u) ≤ Subgroup.centralizer {u} :=
    pSpan_le fun L hL => hL.2
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle y.2))

theorem ae8b2_cm {L : Subgroup G} (hL : L ∈ Generic.centMembers Ω u) (m : G) (hm : m ∈ L) :
    m * u = u * m :=
  Subgroup.mem_centralizer_singleton_iff.mp (hL.2 hm)

theorem ae8b2_zOf_mem (c : Chart Ω u) (H : End18.Hyp Ω) {α : Finset (Fin 6)} (hα : α.card = 4) :
    ∃ y : ↥(pSpan (Generic.centMembers Ω u)), (y : G) ∈ zGroup Ω ∧
      (c.ψ y : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
  obtain ⟨L, hL, hlab⟩ := c.label_surj α hα true
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hL.1
  have hyL : (⟨z, le_pSpan hL hz.mem⟩ : ↥(pSpan (Generic.centMembers Ω u))) ∈
      L.subgroupOf (pSpan (Generic.centMembers Ω u)) := Subgroup.mem_subgroupOf.mpr hz.mem
  have hmem : (c.ψ ⟨z, le_pSpan hL hz.mem⟩ : AE.Wr 6) ∈ AE.memAt α hα true := by
    rw [← hlab]
    exact Subgroup.mem_map.mpr ⟨c.ψ ⟨z, le_pSpan hL hz.mem⟩,
      Subgroup.mem_map.mpr ⟨_, hyL, rfl⟩, rfl⟩
  have h1 : c.ψ ⟨z, le_pSpan hL hz.mem⟩ * c.ψ ⟨z, le_pSpan hL hz.mem⟩ = 1 := by
    rw [← map_mul, show (⟨z, le_pSpan hL hz.mem⟩ : ↥(pSpan (Generic.centMembers Ω u))) *
      ⟨z, le_pSpan hL hz.mem⟩ = 1 from Subtype.ext hz.sq, map_one]
  have hsq : (c.ψ ⟨z, le_pSpan hL hz.mem⟩ : AE.Wr 6) * (c.ψ ⟨z, le_pSpan hL hz.mem⟩ : AE.Wr 6)
      = 1 := congrArg Subtype.val h1
  rcases AE.eq_of_mem_memAt_mul_self hmem hsq with h3 | h3
  · exfalso
    have hy1 : c.ψ ⟨z, le_pSpan hL hz.mem⟩ = 1 := Subtype.ext h3
    have hy2 : (⟨z, le_pSpan hL hz.mem⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 :=
      c.ψ.injective (hy1.trans (map_one c.ψ).symm)
    exact hz.ne_one (congrArg Subtype.val hy2)
  · exact ⟨⟨z, le_pSpan hL hz.mem⟩, Subgroup.subset_closure ⟨L, hL.1, hz⟩, h3⟩

theorem ae8b2_zOf_eq {α : Finset (Fin 6)} (hα : α.card = 4) :
    AE.zOf (AE.emb α hα) = ofVec (ae8b2_ind α) := by
  refine Wr.ext (funext fun x => ?_) (AE.zOf_perm _)
  have hx : x ∈ Set.range (AE.emb α hα) ↔ x ∈ α := by
    rw [AE.range_emb]
    exact Finset.mem_coe
  show (AE.zOf (AE.emb α hα)).vec x = ae8b2_ind α x
  rw [AE.zOf_vec_apply]
  unfold ae8b2_ind
  by_cases h : x ∈ α
  · rw [if_pos h, if_pos (hx.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hx.mp h'))]

theorem ae8b2_zGroup_normal (hΩ : ConjInvariant Ω) : (zGroup Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : n ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨L, hL, hu⟩ := hx
    exact Subgroup.subset_closure ⟨conjSub g L, hΩ g L hL, hu.conj g⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact (zGroup Ω).one_mem
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact (zGroup Ω).mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact (zGroup Ω).inv_mem hx

def ae8b2_cz (i : Fin 6) : Fin 6 := if i = 1 then 2 else 1

theorem ae8b2_cz_spec : ∀ i : Fin 6, i ≠ 0 →
    (Finset.univ \ {0, ae8b2_cz i}).card = 4 ∧ (Finset.univ \ {i, ae8b2_cz i}).card = 4 ∧
      ae8b2_ind (Finset.univ \ {0, ae8b2_cz i}) + ae8b2_ind (Finset.univ \ {i, ae8b2_cz i}) =
        ae8b2_ind {0, i} := by
  unfold ae8b2_cz
  decide

theorem ae8b2_pair (c : Chart Ω u) (H : End18.Hyp Ω) {i : Fin 6} (hi : i ≠ 0) :
    ∃ y : ↥(pSpan (Generic.centMembers Ω u)), (y : G) ∈ zGroup Ω ∧
      (c.ψ y : AE.Wr 6) = ofVec (ae8b2_ind {0, i}) := by
  obtain ⟨h1, h2, h3⟩ := ae8b2_cz_spec i hi
  obtain ⟨y₁, hy₁D, hy₁⟩ := ae8b2_zOf_mem c H h1
  obtain ⟨y₂, hy₂D, hy₂⟩ := ae8b2_zOf_mem c H h2
  refine ⟨y₁ * y₂, Subgroup.mul_mem _ hy₁D hy₂D, ?_⟩
  rw [map_mul]
  show (c.ψ y₁ : AE.Wr 6) * (c.ψ y₂ : AE.Wr 6) = _
  rw [hy₁, hy₂, ae8b2_zOf_eq, ae8b2_zOf_eq, ae8b2_ofVec_mul, h3]

theorem ae8b2_even (c : Chart Ω u) (H : End18.Hyp Ω) (v : Fin 6 → ZMod 2) (hv : ∑ j, v j = 0) :
    ∃ y : ↥(pSpan (Generic.centMembers Ω u)), (y : G) ∈ zGroup Ω ∧
      (c.ψ y : AE.Wr 6) = ofVec v := by
  let Hc : Subgroup (AE.Wr 6) :=
    (((zGroup Ω).subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype
  have hpair : ∀ i : Fin 6, i ≠ 0 → ofVec (ae8b2_ind {0, i}) ∈ Hc := by
    intro i hi
    obtain ⟨y, hyD, hy⟩ := ae8b2_pair c H hi
    exact Subgroup.mem_map.mpr ⟨c.ψ y,
      Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hyD, rfl⟩,
      hy⟩
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp (ae8b2_vec_mem_of_pairs Hc hpair v hv)
  obtain ⟨y, hyD, hyw⟩ := Subgroup.mem_map.mp hw
  refine ⟨y, Subgroup.mem_subgroupOf.mp hyD, ?_⟩
  rw [show c.ψ y = w from hyw]
  exact hwv

theorem ae8b2_perm_of_mem (c : Chart Ω u) (H : End18.Hyp Ω)
    (y : ↥(pSpan (Generic.centMembers Ω u))) (hy : (y : G) ∈ zGroup Ω) :
    (c.ψ y : AE.Wr 6).perm = 1 := by
  have hD : (zGroup Ω).Normal := ae8b2_zGroup_normal H.endHyp.thmD.hyp.conjInvariant
  let N : Subgroup ↥(AE.aeSub 6) :=
    ((zGroup Ω).subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom
  haveI : N.Normal :=
    Subgroup.Normal.map (Subgroup.Normal.subgroupOf hD _) c.ψ.toMonoidHom c.ψ.surjective
  have hsq : ∀ n ∈ N, n * n = 1 := by
    intro n hn
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hn
    have hyy : y' * y' = 1 :=
      Subtype.ext (H.endHyp.zGroup_mul_self H.perp9 _ (Subgroup.mem_subgroupOf.mp hy'))
    have h1 : c.ψ y' * c.ψ y' = 1 := by
      rw [← map_mul, hyy, map_one]
    exact h1
  exact ae8b2_perm_one_of_normal N hsq (c.ψ y)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy))

theorem ae8b2_mem_of_perm (c : Chart Ω u) (H : End18.Hyp Ω)
    (y : ↥(pSpan (Generic.centMembers Ω u))) (hy : (c.ψ y : AE.Wr 6).perm = 1) :
    (y : G) ∈ zGroup Ω := by
  have hsum : ∑ j, (c.ψ y : AE.Wr 6).vec j = 0 := (AE.mem_aeSub.mp (c.ψ y).2).1
  obtain ⟨y', hy'D, hy'⟩ := ae8b2_even c H _ hsum
  have hyy : y' = y := c.ψ.injective (Subtype.ext (hy'.trans (Wr.ext rfl hy.symm)))
  rw [← hyy]
  exact hy'D

theorem ae8b2_comm_top (c : Chart Ω u) :
    ⁅(⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))), ⊤⁆ =
      (⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))) := by
  have hψ : (⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr c.ψ.surjective
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))) ⊤
    c.ψ.toMonoidHom
  rw [hψ] at h
  have h2 : (⁅(⊤ : Subgroup ↥(AE.aeSub 6)), ⊤⁆ : Subgroup ↥(AE.aeSub 6)) = ⊤ :=
    ae8b2_aeSub_comm_top
  rw [h2] at h
  rw [eq_top_iff]
  intro y _
  have hy : c.ψ y ∈ (⁅(⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))), ⊤⁆ :
      Subgroup ↥(pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  rwa [show x = y from c.ψ.injective hxy] at hx

theorem ae8b2_u_mem (c : Chart Ω u) (H : End18.Hyp Ω) : u ∈ zGroup Ω := by
  obtain ⟨y₁, h₁, e₁⟩ := ae8b2_zOf_mem c H (α := {0, 1, 2, 3}) (by decide)
  obtain ⟨y₂, h₂, e₂⟩ := ae8b2_zOf_mem c H (α := {0, 1, 2, 4}) (by decide)
  obtain ⟨y₃, h₃, e₃⟩ := ae8b2_zOf_mem c H (α := {0, 1, 2, 5}) (by decide)
  have hval : (c.ψ (y₁ * y₂ * y₃) : AE.Wr 6) = AE.Wr.allOnes 6 := by
    rw [map_mul, map_mul]
    show (c.ψ y₁ : AE.Wr 6) * (c.ψ y₂ : AE.Wr 6) * (c.ψ y₃ : AE.Wr 6) = _
    rw [e₁, e₂, e₃, ae8b2_zOf_eq, ae8b2_zOf_eq, ae8b2_zOf_eq, ae8b2_ofVec_mul, ae8b2_ofVec_mul]
    rw [show ae8b2_ind {0, 1, 2, 3} + ae8b2_ind {0, 1, 2, 4} + ae8b2_ind {0, 1, 2, 5} =
      fun _ => 1 from by decide]
    rfl
  have hu : c.ψ (y₁ * y₂ * y₃) = c.ψ ⟨u, c.mem⟩ := Subtype.ext (hval.trans c.u_eq.symm)
  have hy : y₁ * y₂ * y₃ = ⟨u, c.mem⟩ := c.ψ.injective hu
  have hu' : ((y₁ * y₂ * y₃ : ↥(pSpan (Generic.centMembers Ω u))) : G) = u :=
    congrArg Subtype.val hy
  rw [← hu']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) h₃

theorem ae8b2_conj_mem (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) (hu : u ∈ zGroup Ω)
    {L : Subgroup G} (hL : L ∈ Generic.centMembers Ω u) :
    conjSub d L ∈ Generic.centMembers Ω u := by
  have hdu : d * u = u * d := H.endHyp.zGroup_comm H.perp9 d hd u hu
  have hconj : d⁻¹ * u * d = u := by
    calc d⁻¹ * u * d = d⁻¹ * (u * d) := by group
      _ = d⁻¹ * (d * u) := by rw [hdu]
      _ = u := by group
  refine ⟨H.endHyp.thmD.hyp.conjInvariant d L hL.1, ?_⟩
  intro m hm
  rw [mem_conjSub_iff] at hm
  have hl := ae8b2_cm hL (d⁻¹ * m * d) hm
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc m * u = d * (d⁻¹ * m * d * (d⁻¹ * u * d)) * d⁻¹ := by group
    _ = d * (d⁻¹ * m * d * u) * d⁻¹ := by rw [hconj]
    _ = d * (u * (d⁻¹ * m * d)) * d⁻¹ := by rw [hl]
    _ = (d * u) * (d⁻¹ * m * d) * d⁻¹ := by group
    _ = (u * d) * (d⁻¹ * m * d) * d⁻¹ := by rw [hdu]
    _ = u * m := by group

theorem ae8b2_conjY_mem (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) (hu : u ∈ zGroup Ω)
    {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u)) :
    d * y * d⁻¹ ∈ pSpan (Generic.centMembers Ω u) := by
  have hle : pSpan (Generic.centMembers Ω u) ≤
      Subgroup.comap (MulAut.conj d).toMonoidHom (pSpan (Generic.centMembers Ω u)) :=
    pSpan_le fun L hL x hx =>
      (show d * x * d⁻¹ ∈ pSpan (Generic.centMembers Ω u) from
        le_pSpan (ae8b2_conj_mem H hd hu hL) (conj_mem_conjSub hx))
  exact hle hy

def ae8b2_cjHom (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) (hu : u ∈ zGroup Ω) :
    ↥(pSpan (Generic.centMembers Ω u)) →* ↥(pSpan (Generic.centMembers Ω u)) where
  toFun y := ⟨d * y * d⁻¹, ae8b2_conjY_mem H hd hu y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem ae8b2_cjHom_cjHom (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) (hu : u ∈ zGroup Ω)
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8b2_cjHom H hd hu (ae8b2_cjHom H ((zGroup Ω).inv_mem hd) hu y) = y := by
  refine Subtype.ext ?_
  show d * (d⁻¹ * (y : G) * d⁻¹⁻¹) * d⁻¹ = y
  group

theorem ae8b2_cjHom_cjHom' (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) (hu : u ∈ zGroup Ω)
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8b2_cjHom H ((zGroup Ω).inv_mem hd) hu (ae8b2_cjHom H hd hu y) = y := by
  refine Subtype.ext ?_
  show d⁻¹ * (d * (y : G) * d⁻¹) * d⁻¹⁻¹ = y
  group

theorem ae8b2_map_cj (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) (hu : u ∈ zGroup Ω)
    (L : Subgroup G) :
    (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map (ae8b2_cjHom H hd hu) =
      (conjSub d L).subgroupOf (pSpan (Generic.centMembers Ω u)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    exact conj_mem_conjSub hx
  · intro hy
    rw [Subgroup.mem_subgroupOf, mem_conjSub_iff] at hy
    refine ⟨ae8b2_cjHom H ((zGroup Ω).inv_mem hd) hu y, ?_, ?_⟩
    · simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      show d⁻¹ * (y : G) * d⁻¹⁻¹ ∈ L
      rw [show d⁻¹ * (y : G) * d⁻¹⁻¹ = d⁻¹ * (y : G) * d by group]
      exact hy
    · exact ae8b2_cjHom_cjHom H hd hu y

theorem ae8b2_twist (c : Chart Ω u) (H : End18.Hyp Ω) (I : AEIdent (Generic.centMembers Ω u) 6)
    {d : G} (hd : d ∈ zGroup Ω) :
    ∃ J : AEIdent (Generic.centMembers Ω u) 6, ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      J.φ y = I.φ (ae8b2_cjHom H hd (ae8b2_u_mem c H) y) := by
  have hu := ae8b2_u_mem c H
  have hdi : d⁻¹ ∈ zGroup Ω := (zGroup Ω).inv_mem hd
  refine ⟨{ φ := I.φ.comp (ae8b2_cjHom H hd hu)
            range_eq := ?_
            ker_le := ?_
            label := ?_
            label_surj := ?_ }, fun y => rfl⟩
  · rw [← I.range_eq]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨ae8b2_cjHom H hd hu y, rfl⟩
    · intro hx
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
      exact MonoidHom.mem_range.mpr ⟨ae8b2_cjHom H hdi hu y, by
        show I.φ (ae8b2_cjHom H hd hu (ae8b2_cjHom H hdi hu y)) = _
        rw [ae8b2_cjHom_cjHom H hd hu y]⟩
  · intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    have hc : ae8b2_cjHom H hd hu y ∈ I.φ.ker := hy
    have hcen := I.ker_le hc
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro g
    have hinj : Function.Injective (ae8b2_cjHom H hd hu) :=
      Function.LeftInverse.injective (g := ae8b2_cjHom H ((zGroup Ω).inv_mem hd) hu)
        (fun y => ae8b2_cjHom_cjHom' H hd hu y)
    apply hinj
    rw [map_mul, map_mul]
    exact hcen (ae8b2_cjHom H hd hu g)
  · intro L hL
    obtain ⟨α, h, b, hlab⟩ := I.label (conjSub d L) (ae8b2_conj_mem H hd hu hL)
    refine ⟨α, h, b, ?_⟩
    rw [← Subgroup.map_map, ae8b2_map_cj H hd hu L, hlab]
  · intro α h b
    obtain ⟨L', hL', hlab⟩ := I.label_surj α h b
    refine ⟨conjSub d⁻¹ L', ae8b2_conj_mem H hdi hu hL', ?_⟩
    rw [← Subgroup.map_map, ae8b2_map_cj H hd hu, conjSub_conjSub_inv, hlab]

theorem ae8b2_chart_ident (c : Chart Ω u) :
    ∃ I : AEIdent (Generic.centMembers Ω u) 6, ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      I.φ y = AE.mkQ 6 (c.ψ y : AE.Wr 6) := by
  refine ⟨{ φ := (AE.mkQ 6).comp ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom)
            range_eq := ?_
            ker_le := ?_
            label := ?_
            label_surj := ?_ }, fun y => rfl⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(c.ψ y : AE.Wr 6), (c.ψ y).2, rfl⟩
    · intro hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y, hy⟩ := c.ψ.surjective ⟨g, hg⟩
      exact MonoidHom.mem_range.mpr ⟨y, congrArg (AE.mkQ 6) (congrArg Subtype.val hy)⟩
  · intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply] at hy
    have h1 : (c.ψ y : AE.Wr 6) ∈ AE.piSub 6 := (QuotientGroup.eq_one_iff _).mp hy
    rcases AE.mem_piSub.mp h1 with h | h
    · have hy1 : y = 1 := c.ψ.injective (Subtype.ext h |>.trans (map_one c.ψ).symm)
      rw [hy1]
      exact Subgroup.one_mem _
    · have hy1 : y = ⟨u, c.mem⟩ := c.ψ.injective (Subtype.ext (h.trans c.u_eq.symm))
      rw [hy1, Subgroup.mem_center_iff]
      intro g
      exact ae8b2_u_central c g
  · intro L hL
    obtain ⟨α, h, b, hlab⟩ := c.label L hL
    refine ⟨α, h, b, ?_⟩
    have key : (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map
        ((AE.mkQ 6).comp ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom)) =
        (((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
          (AE.aeSub 6).subtype).map (AE.mkQ 6) := by
      simp only [Subgroup.map_map]
    rw [key, hlab]
    rfl
  · intro α h b
    obtain ⟨L, hL, hlab⟩ := c.label_surj α h b
    refine ⟨L, hL, ?_⟩
    have key : (L.subgroupOf (pSpan (Generic.centMembers Ω u))).map
        ((AE.mkQ 6).comp ((AE.aeSub 6).subtype.comp c.ψ.toMonoidHom)) =
        (((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
          (AE.aeSub 6).subtype).map (AE.mkQ 6) := by
      simp only [Subgroup.map_map]
    rw [key, hlab]
    rfl

theorem ae8b2_cjHom_mul (H : End18.Hyp Ω) {d d' : G} (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω)
    (hu : u ∈ zGroup Ω) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8b2_cjHom H ((zGroup Ω).mul_mem hd hd') hu y =
      ae8b2_cjHom H hd hu (ae8b2_cjHom H hd' hu y) := by
  refine Subtype.ext ?_
  show d * d' * (y : G) * (d * d')⁻¹ = d * (d' * (y : G) * d'⁻¹) * d⁻¹
  group

theorem ae8b2_cjHom_one (H : End18.Hyp Ω) (hu : u ∈ zGroup Ω)
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8b2_cjHom H ((zGroup Ω).one_mem) hu y = y := by
  refine Subtype.ext ?_
  show 1 * (y : G) * (1 : G)⁻¹ = y
  group

theorem ae8b2_exists_theta (c : Chart Ω u) (H : End18.Hyp Ω) :
    ∃ θ : ↥(zGroup Ω) →* AE.AEQ 6,
      (∀ d, ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v)) ∧
      ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
        (y' : G) = d * y * d⁻¹ →
          AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹ := by
  obtain ⟨I, hI⟩ := ae8b2_chart_ident c
  have hu := ae8b2_u_mem c H
  have hex : ∀ (d : G) (hd : d ∈ zGroup Ω), ∃ x : AE.AEQ 6,
      ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
        I.φ (ae8b2_cjHom H hd hu y) = x * I.φ y * x⁻¹ := by
    intro d hd
    obtain ⟨J, hJ⟩ := ae8b2_twist c H I hd
    obtain ⟨x, hx⟩ := AEIdent.exists_conj_of_model117 (by norm_num) model117At_six I J
    exact ⟨x, fun y => by rw [← hJ y]; exact hx y⟩
  have huniq : ∀ (d : G) (hd : d ∈ zGroup Ω) (x x' : AE.AEQ 6),
      (∀ y : ↥(pSpan (Generic.centMembers Ω u)),
        I.φ (ae8b2_cjHom H hd hu y) = x * I.φ y * x⁻¹) →
      (∀ y : ↥(pSpan (Generic.centMembers Ω u)),
        I.φ (ae8b2_cjHom H hd hu y) = x' * I.φ y * x'⁻¹) → x = x' := by
    intro d hd x x' hx hx'
    have hc : x'⁻¹ * x = 1 := by
      apply ae8b2_cent_trivial
      intro g hg
      have hg' : g ∈ I.φ.range := by
        rw [I.range_eq]
        exact hg
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg'
      calc x'⁻¹ * x * I.φ y = x'⁻¹ * (x * I.φ y * x⁻¹) * x := by group
        _ = x'⁻¹ * (x' * I.φ y * x'⁻¹) * x := by rw [← hx y, ← hx' y]
        _ = I.φ y * (x'⁻¹ * x) := by group
    exact (inv_mul_eq_one.mp hc).symm
  have hchoose : ∀ d : ↥(zGroup Ω), ∃ x : AE.AEQ 6,
      ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
        I.φ (ae8b2_cjHom H d.2 hu y) = x * I.φ y * x⁻¹ := fun d => hex d.1 d.2
  choose θf hθf using hchoose
  have hone : θf 1 = 1 := by
    refine huniq _ _ _ _ (hθf 1) (fun y => ?_)
    rw [ae8b2_cjHom_one H hu y]
    simp
  have hmul : ∀ d d' : ↥(zGroup Ω), θf (d * d') = θf d * θf d' := by
    intro d d'
    refine huniq _ _ _ _ (hθf (d * d')) (fun y => ?_)
    rw [ae8b2_cjHom_mul H d.2 d'.2 hu y, hθf d (ae8b2_cjHom H d'.2 hu y), hθf d' y]
    group
  let θ : ↥(zGroup Ω) →* AE.AEQ 6 :=
    { toFun := θf
      map_one' := hone
      map_mul' := hmul }
  refine ⟨θ, ?_, ?_⟩
  · intro d
    have hcomm : ∀ i : Fin 6, i ≠ 0 →
        AE.mkQ 6 (AE.Wr.ofVec (ae8b2_ind {0, i})) * θf d =
          θf d * AE.mkQ 6 (AE.Wr.ofVec (ae8b2_ind {0, i})) := by
      intro i hi
      obtain ⟨y, hyD, hyψ⟩ := ae8b2_pair c H hi
      have hdy : ae8b2_cjHom H d.2 hu y = y := by
        refine Subtype.ext ?_
        show d.1 * (y : G) * d.1⁻¹ = y
        have hc := H.endHyp.zGroup_comm H.perp9 d.1 d.2 (y : G) hyD
        calc d.1 * (y : G) * d.1⁻¹ = (y : G) * d.1 * d.1⁻¹ := by rw [hc]
          _ = (y : G) := by group
      have h := hθf d y
      rw [hdy] at h
      have hIy : I.φ y = AE.mkQ 6 (AE.Wr.ofVec (ae8b2_ind {0, i})) := by
        rw [hI y, hyψ]
      rw [hIy] at h
      calc AE.mkQ 6 (AE.Wr.ofVec (ae8b2_ind {0, i})) * θf d
          = (θf d * AE.mkQ 6 (AE.Wr.ofVec (ae8b2_ind {0, i})) * (θf d)⁻¹) * θf d := by
            rw [← h]
        _ = θf d * AE.mkQ 6 (AE.Wr.ofVec (ae8b2_ind {0, i})) := by group
    obtain ⟨v, hv⟩ := ae8b2_vec_of_comm_pairs (θf d) hcomm
    exact ⟨v, hv⟩
  · intro d y y' h
    have hy' : y' = ae8b2_cjHom H d.2 hu y := Subtype.ext h
    calc AE.mkQ 6 (c.ψ y' : AE.Wr 6) = I.φ y' := (hI y').symm
      _ = I.φ (ae8b2_cjHom H d.2 hu y) := by rw [hy']
      _ = θf d * I.φ y * (θf d)⁻¹ := hθf d y
      _ = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹ := by rw [hI y]; rfl

end Ae8b2Aux

theorem mem_zGroup_iff (H : End18.Hyp Ω) (y : ↥(pSpan (Generic.centMembers Ω u))) :
    (y : G) ∈ zGroup Ω ↔ (c.ψ y : AE.Wr 6).perm = 1 := by
  exact ⟨fun hy => ae8b2_perm_of_mem c H y hy, fun hy => ae8b2_mem_of_perm c H y hy⟩

include c in
theorem perfect : commutator ↥(pSpan (Generic.centMembers Ω u)) = ⊤ := by
  exact ae8b2_comm_top c

theorem exists_vecAct (H : End18.Hyp Ω) :
    ∃ θ : ↥(zGroup Ω) →* AE.AEQ 6,
      (∀ d, ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v)) ∧
      ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
        (y' : G) = d * y * d⁻¹ →
          AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹ := by
  exact ae8b2_exists_theta c H

theorem ae8b2_ker_sub (c : Chart Ω u) (H : End18.Hyp Ω)
    (hC : ∀ d ∈ zGroup Ω,
      d ∈ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) →
        d ∈ Subgroup.zpowers u)
    (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
        (y' : G) = d * y * d⁻¹ →
          AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    (d : ↥(zGroup Ω)) (hd : θ d = 1) : (d : G) ∈ Subgroup.zpowers u := by
  have hu := ae8b2_u_mem c H
  have hk : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      y⁻¹ * ae8b2_cjHom H d.2 hu y = 1 ∨ y⁻¹ * ae8b2_cjHom H d.2 hu y = ⟨u, c.mem⟩ := by
    intro y
    have h1 := hθ d y (ae8b2_cjHom H d.2 hu y) rfl
    rw [hd, one_mul, inv_one, mul_one] at h1
    have h2 := (AE.mkQ_eq_iff (a := (c.ψ y : AE.Wr 6))
      (b := (c.ψ (ae8b2_cjHom H d.2 hu y) : AE.Wr 6))).mp
      h1.symm
    have h3 : c.ψ (y⁻¹ * ae8b2_cjHom H d.2 hu y) =
        (c.ψ y)⁻¹ * c.ψ (ae8b2_cjHom H d.2 hu y) := by rw [map_mul, map_inv]
    have h4 : ((c.ψ (y⁻¹ * ae8b2_cjHom H d.2 hu y) : ↥(AE.aeSub 6)) : AE.Wr 6) =
        (c.ψ y : AE.Wr 6)⁻¹ * (c.ψ (ae8b2_cjHom H d.2 hu y) : AE.Wr 6) := by
      rw [h3]
      rfl
    rcases h2 with h5 | h5
    · left
      apply c.ψ.injective
      rw [map_one]
      refine Subtype.ext ?_
      rw [h4, h5]
      rfl
    · right
      apply c.ψ.injective
      refine Subtype.ext ?_
      rw [h4, h5, c.u_eq]
  have hcen : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      y⁻¹ * ae8b2_cjHom H d.2 hu y ∈ Subgroup.center ↥(pSpan (Generic.centMembers Ω u)) := by
    intro y
    rcases hk y with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_center_iff.mpr (fun g => ae8b2_u_central c g)
  let gH : ↥(pSpan (Generic.centMembers Ω u)) →* ↥(pSpan (Generic.centMembers Ω u)) :=
    { toFun := fun y => y⁻¹ * ae8b2_cjHom H d.2 hu y
      map_one' := by simp only [inv_one, map_one, one_mul]
      map_mul' := fun a b => by
        show (a * b)⁻¹ * ae8b2_cjHom H d.2 hu (a * b) =
          (a⁻¹ * ae8b2_cjHom H d.2 hu a) * (b⁻¹ * ae8b2_cjHom H d.2 hu b)
        rw [map_mul]
        calc (a * b)⁻¹ * (ae8b2_cjHom H d.2 hu a * ae8b2_cjHom H d.2 hu b)
            = b⁻¹ * (a⁻¹ * ae8b2_cjHom H d.2 hu a) * ae8b2_cjHom H d.2 hu b := by group
          _ = (a⁻¹ * ae8b2_cjHom H d.2 hu a) * b⁻¹ * ae8b2_cjHom H d.2 hu b := by
            rw [Subgroup.mem_center_iff.mp (hcen a) b⁻¹]
          _ = (a⁻¹ * ae8b2_cjHom H d.2 hu a) * (b⁻¹ * ae8b2_cjHom H d.2 hu b) := by group }
  have hle : ⁅(⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))), ⊤⁆ ≤ gH.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    have hc : gH a * gH b = gH b * gH a :=
      ((Subgroup.mem_center_iff.mp (hcen a)) (gH b)).symm
    show gH (a * b * a⁻¹ * b⁻¹) = 1
    simp only [map_mul, map_inv]
    calc gH a * gH b * (gH a)⁻¹ * (gH b)⁻¹ = gH b * gH a * (gH a)⁻¹ * (gH b)⁻¹ := by rw [hc]
      _ = 1 := by group
  have htop : (⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))) ≤ gH.ker := by
    calc (⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u)))
        = ⁅(⊤ : Subgroup ↥(pSpan (Generic.centMembers Ω u))), ⊤⁆ :=
          (ae8b2_comm_top c).symm
      _ ≤ gH.ker := hle
  have hcj : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      ae8b2_cjHom H d.2 hu y = y := by
    intro y
    have h' : y⁻¹ * ae8b2_cjHom H d.2 hu y = 1 := (MonoidHom.mem_ker.mp (htop (Subgroup.mem_top y)))
    exact (inv_mul_eq_one.mp h').symm
  have hcent : (d : G) ∈ Subgroup.centralizer
      ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hy : (d : G) * h * (d : G)⁻¹ = h := congrArg Subtype.val (hcj ⟨h, hh⟩)
    calc h * (d : G) = (d * h * (d : G)⁻¹) * (d : G) := by rw [hy]
      _ = (d : G) * h := by group
  exact hC _ d.2 hcent

theorem ae8b2_range_le (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθv : ∀ d : ↥(zGroup Ω), ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v)) :
    Nat.card θ.range ≤ 32 := by
  let F : {v : Fin 6 → ZMod 2 // v 0 = 0} → AE.AEQ 6 := fun v => AE.mkQ 6 (AE.Wr.ofVec v.1)
  have hsub : ∀ x ∈ θ.range, x ∈ Set.range F := by
    intro x hx
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨v, hv⟩ := hθv d
    obtain ⟨v', hv0, hv'⟩ := ae8b2_normalize v
    exact ⟨⟨v', hv0⟩, by show AE.mkQ 6 (AE.Wr.ofVec v') = θ d; rw [hv', hv]⟩
  have h1 : Nat.card θ.range ≤ Nat.card (Set.range F) := by
    apply Nat.card_le_card_of_injective (fun x => (⟨x.1, hsub x.1 x.2⟩ : Set.range F))
    intro x y hxy
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    exact h
  have h2 : Nat.card (Set.range F) ≤ Nat.card {v : Fin 6 → ZMod 2 // v 0 = 0} :=
    Finite.card_range_le F
  have h3 : Nat.card {v : Fin 6 → ZMod 2 // v 0 = 0} = 32 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

theorem ae8b2_card_le (c : Chart Ω u) (H : End18.Hyp Ω) (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθv : ∀ d : ↥(zGroup Ω), ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v))
    (hker : ∀ d : ↥(zGroup Ω), θ d = 1 → (d : G) ∈ Subgroup.zpowers u) :
    Nat.card ↥(zGroup Ω) ≤ 64 := by
  have hu2 : u * u = 1 := H.endHyp.zGroup_mul_self H.perp9 u (ae8b2_u_mem c H)
  have hord : Nat.card (Subgroup.zpowers u) ≤ 2 := by
    rw [Nat.card_zpowers]
    have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    exact Nat.le_of_dvd (by norm_num) h2
  have hk : Nat.card θ.ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : θ.ker => (⟨(x : ↥(zGroup Ω)).1, hker x.1 (MonoidHom.mem_ker.mp x.2)⟩ :
        Subgroup.zpowers u)) ?_) hord
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    exact h
  have hr := ae8b2_range_le θ hθv
  have hdecomp := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have hquot : Nat.card (↥(zGroup Ω) ⧸ θ.ker) = Nat.card θ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
  rw [hdecomp, hquot]
  exact Nat.mul_le_mul hr hk

theorem ae8b2_card_ge (H : End18.Hyp Ω) : 64 ≤ Nat.card ↥(zGroup Ω) := by
  obtain ⟨K, hK, -, -, -⟩ := H.endHyp.exists_ne
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hK
  obtain ⟨J, hJ, s, hsJ, hsK⟩ := H.exists_swap hK
  have hs : s ∈ zGroup Ω := Subgroup.subset_closure ⟨J, hJ, hsJ⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsJ.sq
  have hss : ∀ L : Subgroup G, conjSub s (conjSub s L) = L := fun L => by
    have := conjSub_inv_conjSub s L
    rwa [hsinv] at this
  have hKT : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hKs : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  obtain ⟨K₃, hK₃T, hK₃K, hK₃s⟩ : ∃ K₃ ∈ twinSet Ω K, K₃ ≠ K ∧ K₃ ≠ conjSub s K := by
    by_contra hcon
    push Not at hcon
    have hsub : twinSet Ω K ⊆ {K, conjSub s K} := by
      intro L hL
      by_cases hLK : L = K
      · exact Or.inl hLK
      · exact Or.inr (hcon L hL hLK)
    have h4 := H.ncard_twinSet hK
    have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({K, conjSub s K} : Set (Subgroup G)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have hK₃Ω : K₃ ∈ Ω := hK₃T.1
  obtain ⟨τ, hτfix, -, hτact⟩ := H.exists_twin_involution hK
  have hτs : ∀ L : ↥(twinSet Ω K),
      conjSub s (L : Subgroup G) = ((τ L : ↥(twinSet Ω K)) : Subgroup G) := by
    rcases hτact s hs with h | h
    · exfalso
      exact hsK (h ⟨K, hKT⟩)
    · exact h
  have hK₄eq : conjSub s K₃ = ((τ ⟨K₃, hK₃T⟩ : ↥(twinSet Ω K)) : Subgroup G) :=
    hτs ⟨K₃, hK₃T⟩
  have hK₄T : conjSub s K₃ ∈ twinSet Ω K := by
    rw [hK₄eq]
    exact (τ ⟨K₃, hK₃T⟩).2
  have hK₃s' : conjSub s K₃ ≠ K₃ := by
    intro h
    apply hτfix ⟨K₃, hK₃T⟩
    apply Subtype.ext
    rw [← hK₄eq]
    exact h
  have hK₄K : conjSub s K₃ ≠ K := by
    intro h
    apply hK₃s
    rw [← hss K₃, h]
  have hcomm3 : Commutes K K₃ := (H.sup_twin hz hKT hK₃T hK₃K.symm).1
  have hcomm4 : Commutes K (conjSub s K₃) := (H.sup_twin hz hKT hK₄T hK₄K.symm).1
  have hcard8 : Nat.card ↥(zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃)) = 8 :=
    H.card_dZero hK₃Ω hs hK₃s'
  have hle : zGroup Ω ⊓ (K₃ ⊔ conjSub s K₃) ≤ zGroup Ω ⊓ Subgroup.centralizer (K : Set G) := by
    refine inf_le_inf_left _ (sup_le ?_ ?_)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hcomm3 h hh y hy
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hcomm4 h hh y hy
  have h8 : 8 ≤ Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← hcard8]
    exact Subgroup.card_le_of_le hle
  have hmul := H.card_inf_centralizer_mul_eight hK
  omega

end Chart

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13

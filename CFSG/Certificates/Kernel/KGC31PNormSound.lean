module

public import Certificates.Data.Kernel.KGC31PNorm
public import CFSG.Certificates.Kernel.KGC31PPow

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK

variable {n w : Nat}

@[expose] noncomputable def spanG (n w : Nat) (bs : List Nat) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {x | ∃ b ∈ bs, sg n w b = x}

theorem pc_pidn (hsz : szOK n w = true) {c : Nat} (hc : PP n w c) : pc n w (pidn n w) c = c :=
  (PP_eq_iff ((PP.id hsz).pc hc) hc).2 (by rw [sg_pc (PP.id hsz) hc, sg_id hsz, one_mul])

theorem mem_normalizer_of_conj_fin {G : Type} [Group G] [Finite G] {K : Subgroup G} {x : G}
    (h : ∀ b ∈ K, x * b * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨h b, fun hb => ?_⟩
  let F : K → K := fun c => ⟨x * c * x⁻¹, h c c.2⟩
  have hF : Function.Injective F := fun c c' e => Subtype.ext (by
    have e' : x * (c : G) * x⁻¹ = x * c' * x⁻¹ := congrArg Subtype.val e
    simpa using e')
  obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 hF ⟨_, hb⟩
  have e : x * (c : G) * x⁻¹ = x * b * x⁻¹ := congrArg Subtype.val hc
  have e' : (c : G) = b := by simpa using e
  rw [← e']
  exact c.2

theorem pinSpan_iff (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b) {t : Nat}
    (ht : PP n w t) : pinSpan n w bs t = true ↔ ∃ s ∈ pspan n w bs, sg n w s = sg n w t := by
  unfold pinSpan
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, hs, e⟩
    exact ⟨s, hs, (congrArg (sg n w) (Nat.eq_of_beq_eq_true e)).symm⟩
  · rintro ⟨s, hs, e⟩
    exact ⟨s, hs, Nat.beq_eq.mpr ((PP_eq_iff ht (PP_pspan hsz hb s hs)).2 e.symm)⟩

theorem sg_pmask_mem (hsz : szOK n w = true) {K : Subgroup (Equiv.Perm (Fin n))} :
    ∀ (L : List Nat), (∀ b ∈ L, PP n w b) → (∀ b ∈ L, sg n w b ∈ K) →
      ∀ m, sg n w (pmask n w L m) ∈ K
  | [], _, _, m => by
    unfold pmask
    rw [sg_id hsz]
    exact K.one_mem
  | b :: L, hp, hk, m => by
    have hp' : ∀ c ∈ L, PP n w c := fun c hc => hp c (List.mem_cons_of_mem _ hc)
    have hk' : ∀ c ∈ L, sg n w c ∈ K := fun c hc => hk c (List.mem_cons_of_mem _ hc)
    have hsel : PP n w (if m % 2 = 1 then b else pidn n w) ∧
        sg n w (if m % 2 = 1 then b else pidn n w) ∈ K := by
      split
      · exact ⟨hp b List.mem_cons_self, hk b List.mem_cons_self⟩
      · exact ⟨PP.id hsz, by rw [sg_id hsz]; exact K.one_mem⟩
    unfold pmask
    rw [sg_pc hsel.1 (PP_pmask hsz L hp' _)]
    exact K.mul_mem hsel.2 (sg_pmask_mem hsz L hp' hk' _)

theorem mem_spanG_iff (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) {x : Equiv.Perm (Fin n)} :
    x ∈ spanG n w bs ↔ ∃ s ∈ pspan n w bs, sg n w s = x := by
  have hpp := PP_pspan hsz hb
  unfold pspanOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  unfold spanG
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb', rfl⟩ := hx
      exact (pinSpan_iff hsz hb (hb b hb')).1 (h2 b hb')
    | one =>
      obtain ⟨s, hs, e⟩ := (pinSpan_iff hsz hb (PP.id hsz)).1 h1
      exact ⟨s, hs, e.trans (sg_id hsz)⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨s, hs, rfl⟩ := ihx
      obtain ⟨t, ht, rfl⟩ := ihy
      obtain ⟨u, hu, e⟩ := (pinSpan_iff hsz hb ((hpp s hs).pc (hpp t ht))).1 ((h3 s hs).2 t ht)
      exact ⟨u, hu, e.trans (sg_pc (hpp s hs) (hpp t ht))⟩
    | inv x _ ihx =>
      obtain ⟨s, hs, rfl⟩ := ihx
      obtain ⟨u, hu, e⟩ := (pinSpan_iff hsz hb (hpp s hs).pinv).1 (h3 s hs).1
      exact ⟨u, hu, e.trans (sg_pinv' (hpp s hs))⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hs
    exact sg_pmask_mem hsz bs hb
      (fun b hb' => Subgroup.subset_closure (k := {x | ∃ b ∈ bs, sg n w b = x}) ⟨b, hb', rfl⟩) m

theorem pnormAll_iff (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) {T : Nat} (hT : PP n w T) :
    pnormAll n w bs T (pinv n w T) = true ↔
      sg n w T ∈ Subgroup.normalizer (spanG n w bs : Set (Equiv.Perm (Fin n))) := by
  have hcj : ∀ b ∈ bs, sg n w (pcj n w T (pinv n w T) b) =
      sg n w T * sg n w b * (sg n w T)⁻¹ := fun b hb' => by
    unfold pcj
    rw [sg_pc (hT.pc (hb b hb')) hT.pinv, sg_pc hT (hb b hb'), sg_pinv' hT]
  have hpp := PP_pspan hsz hb
  unfold pnormAll
  rw [List.all_eq_true]
  constructor
  · intro h
    have hgen : ∀ b ∈ bs, sg n w T * sg n w b * (sg n w T)⁻¹ ∈ spanG n w bs := fun b hb' => by
      obtain ⟨s, hs, e⟩ := List.any_eq_true.1 (h b hb')
      rw [← hcj b hb', Nat.eq_of_beq_eq_true e]
      exact (mem_spanG_iff hsz hb hok).2 ⟨s, hs, rfl⟩
    refine mem_normalizer_of_conj_fin fun k hk => ?_
    unfold spanG at hgen hk ⊢
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb', rfl⟩ := hx
      exact hgen b hb'
    | one => simpa using (Subgroup.closure {x | ∃ b ∈ bs, sg n w b = x}).one_mem
    | mul x y _ _ ihx ihy =>
      have := (Subgroup.closure {x | ∃ b ∈ bs, sg n w b = x}).mul_mem ihx ihy
      simpa [mul_assoc] using this
    | inv x _ ihx =>
      have := (Subgroup.closure {x | ∃ b ∈ bs, sg n w b = x}).inv_mem ihx
      simpa [mul_assoc] using this
  · intro h b hb'
    have hm : sg n w T * sg n w b * (sg n w T)⁻¹ ∈ spanG n w bs :=
      (Subgroup.mem_normalizer_iff.1 h _).1 (Subgroup.subset_closure ⟨b, hb', rfl⟩)
    obtain ⟨s, hs, e⟩ := (mem_spanG_iff hsz hb hok).1 hm
    exact List.any_eq_true.2 ⟨s, hs, Nat.beq_eq.mpr
      ((PP_eq_iff (PP_pcj hT hT.pinv (hb b hb')) (hpp s hs)).2 ((hcj b hb').trans e.symm))⟩

theorem pnormAll_left (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) {r c : Nat} (hr : PP n w r) (hc : PP n w c)
    (h1 : pnormAll n w bs (pc n w r c) (pinv n w (pc n w r c)) = true)
    (h2 : pnormAll n w bs c (pinv n w c) = true) : pnormAll n w bs r (pinv n w r) = true := by
  rw [pnormAll_iff hsz hb hok (hr.pc hc), sg_pc hr hc] at h1
  rw [pnormAll_iff hsz hb hok hc] at h2
  rw [pnormAll_iff hsz hb hok hr]
  simpa using Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

theorem countP_pnormAll_eq_zero (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hok : pspanOK n w bs = true) {L : List Nat} (hL : ∀ c ∈ L, PP n w c)
    (h0 : ∀ c ∈ L, pnormAll n w bs c (pinv n w c) = true) {r : Nat} (hr : PP n w r)
    (hn : pnormAll n w bs r (pinv n w r) = false) :
    L.countP (fun c => pnormAll n w bs (pc n w r c) (pinv n w (pc n w r c))) = 0 := by
  rw [List.countP_eq_zero]
  intro c hc e
  rw [pnormAll_left hsz hb hok hr (hL c hc) e (h0 c hc)] at hn
  exact absurd hn (by decide)

end CFSG.KC.KGC31P

end

module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltModFix
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp

variable {V : Type} [CommGroup V]

private theorem caw_commV_norm {Y : Subgroup (MulAut V)} {c : MulAut V}
    (hnorm : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) {w : V} (hw : w ∈ commV Y) : c w ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hnorm hw

private theorem caw_mem_stab {m : ℕ} {σ : alternatingGroup (Fin m)} {c : Fin m} :
    σ ∈ altStabilizer m {c} ↔ (σ : Equiv.Perm (Fin m)) c = c := by
  simp only [altStabilizer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, Finset.mem_singleton,
    forall_eq]
  exact Iff.rfl

private theorem caw_exists_off {m : ℕ} {S : Finset (Fin m)} (hS : S.card < m) :
    ∃ x : Fin m, x ∉ S := by
  by_contra hcon
  have := Finset.eq_univ_of_forall fun x => Classical.byContradiction fun hx => hcon ⟨x, hx⟩
  rw [this, Finset.card_univ, Fintype.card_fin] at hS
  exact lt_irrefl _ hS

private theorem caw_exists_perm {m : ℕ} (hm : 7 ≤ m) {F : Finset (Fin m)} (hF : F.card ≤ 3)
    {i j : Fin m} (hi : i ∉ F) (hj : j ∉ F) :
    ∃ σ : alternatingGroup (Fin m), (∀ f ∈ F, (σ : Equiv.Perm (Fin m)) f = f) ∧
      (σ : Equiv.Perm (Fin m)) i = j := by
  classical
  by_cases hij : i = j
  · exact ⟨1, fun f _ => rfl, hij⟩
  have hcard : 1 < (insert i (insert j F))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have h1 := Finset.card_insert_le i (insert j F)
    have h2 := Finset.card_insert_le j F
    omega
  obtain ⟨l, hl, n, hn, hln⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hl hn
  refine ⟨⟨Equiv.swap i j * Equiv.swap l n, ?_⟩, fun f hf => ?_, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hij, hln]
  · have hfi : f ≠ i := fun h => hi (h ▸ hf)
    have hfj : f ≠ j := fun h => hj (h ▸ hf)
    have hfl : f ≠ l := fun h => hl.2.2 (h ▸ hf)
    have hfn : f ≠ n := fun h => hn.2.2 (h ▸ hf)
    show (Equiv.swap i j) ((Equiv.swap l n) f) = f
    rw [Equiv.swap_apply_of_ne_of_ne hfl hfn, Equiv.swap_apply_of_ne_of_ne hfi hfj]
  · show (Equiv.swap i j) ((Equiv.swap l n) i) = j
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hl.1) (Ne.symm hn.1), Equiv.swap_apply_left]

private theorem caw_exists_fam {m : ℕ} (hodd : Odd m) (hm : 5 ≤ m) {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) (hnat : IsNatSectionWith (altAct m) θ (commV Y) ⊥) :
    ∃ w : Fin m → V, (∀ p, w p ∈ commV Y ∧ w p ≠ 1) ∧
      (∀ (p : Fin m) (y : MulAut V) (hy : y ∈ Y),
        (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p → y (w p) = w p) ∧
      (∀ (p : Fin m) (u : V), u ∈ commV Y →
        (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p → y u = u) →
        u = 1 ∨ u = w p) := by
  have key : ∀ c : Fin m, ∃ w : V, w ∈ commV Y ∧ w ≠ 1 ∧
      (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) c = c → y w = w) ∧
      (∀ u : V, u ∈ commV Y →
        (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) c = c → y u = u) →
        u = 1 ∨ u = w) := by
    intro c
    let N : Subgroup (MulAut V) := ((altStabilizer m {c}).comap θ.toMonoidHom).map Y.subtype
    have hNY : N ≤ Y := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hN : (N.subgroupOf Y).map θ.toMonoidHom = altStabilizer m {c} := by
      have h1 : N.subgroupOf Y = (altStabilizer m {c}).comap θ.toMonoidHom :=
        Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
      rw [h1, Subgroup.map_comap_eq_self_of_surjective θ.surjective]
    have hmemN : ∀ (y : MulAut V) (hy : y ∈ Y),
        y ∈ N ↔ (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) c = c := by
      intro y hy
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact caw_mem_stab.mp hz
      · intro h
        exact ⟨⟨y, hy⟩, caw_mem_stab.mpr h, rfl⟩
    obtain ⟨w, hw1, hwN, hwfix, hw⟩ := exists_fixed_pair_of_natural hodd hm θ hnat hNY c hN
    refine ⟨w, commV_mono hNY hwN, hw1,
      fun y hy h => mem_fixV.mp hwfix y ((hmemN y hy).mpr h), fun u hu hufix => ?_⟩
    refine hw u hu fun n hn => ?_
    have hnY : n ∈ Y := hNY hn
    exact hufix n hnY ((hmemN n hnY).mp hn)
  choose w hw1 hw2 hw3 hw4 using key
  exact ⟨w, fun p => ⟨hw1 p, hw2 p⟩, hw3, hw4⟩

private theorem caw_apply {m : ℕ} {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {w : Fin m → V}
    (hmem : ∀ p, w p ∈ commV Y ∧ w p ≠ 1)
    (hfix : ∀ (p : Fin m) (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p → y (w p) = w p)
    (huniq : ∀ (p : Fin m) (u : V), u ∈ commV Y →
      (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p → y u = u) →
      u = 1 ∨ u = w p)
    {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hs' : ∀ y ∈ Y, s⁻¹ * y * s ∈ Y)
    {π : Equiv.Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Equiv.Perm (Fin m)) =
        π * (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) * π⁻¹) (p : Fin m) :
    s (w p) = w (π p) := by
  have h1 : s (w p) ∈ commV Y := caw_commV_norm hs (hmem p).1
  have h2 : s (w p) ≠ 1 := fun h => (hmem p).2 ((map_eq_one_iff s s.injective).mp h)
  have h3 : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) (π p) = π p → y (s (w p)) = s (w p) := by
    intro y hy hyp
    have hy' := hs' y hy
    have e1 : (⟨s * (s⁻¹ * y * s) * s⁻¹, hs _ hy'⟩ : ↥Y) = ⟨y, hy⟩ := Subtype.ext (by group)
    have e2 : (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) =
        π * (θ ⟨s⁻¹ * y * s, hy'⟩ : Equiv.Perm (Fin m)) * π⁻¹ := by
      rw [← e1]
      exact hπ _ hy'
    have e3 : (θ ⟨s⁻¹ * y * s, hy'⟩ : Equiv.Perm (Fin m)) p = p := by
      have : (θ ⟨s⁻¹ * y * s, hy'⟩ : Equiv.Perm (Fin m)) = π⁻¹ * θ ⟨y, hy⟩ * π := by
        rw [e2]
        group
      rw [this]
      simp [Equiv.Perm.mul_apply, hyp]
    have e4 := hfix p _ hy' e3
    have e5 : y * s = s * (s⁻¹ * y * s) := by group
    calc y (s (w p)) = (y * s) (w p) := rfl
      _ = (s * (s⁻¹ * y * s)) (w p) := by rw [e5]
      _ = s ((s⁻¹ * y * s) (w p)) := rfl
      _ = s (w p) := by rw [e4]
  rcases huniq (π p) _ h1 h3 with h | h
  · exact absurd h h2
  · exact h

theorem exists_wfam [Finite V] {m : ℕ} (hodd : Odd m) (hm : 7 ≤ m) {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) (hnat : IsNatSectionWith (altAct m) θ (commV Y) ⊥) :
    ∃ w : Fin m → V,
      (∀ p, w p ∈ commV Y ∧ w p ≠ 1) ∧ Function.Injective w ∧
      (∀ (y : MulAut V) (hy : y ∈ Y) (p : Fin m),
        y (w p) = w ((θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p)) ∧
      Subgroup.closure (Set.range w) = commV Y ∧
      (∀ (p : Fin m) (u : V), u ∈ commV Y →
        (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p → y u = u) →
        u = 1 ∨ u = w p) ∧
      (∀ p q p' q' : Fin m, p ≠ q → p ≠ p' → p ≠ q' → q ≠ p' → q ≠ q' → p' ≠ q' →
        w p * w q * w p' * w q' ≠ 1) := by
  classical
  obtain ⟨w, hmem, hfix, huniq⟩ := caw_exists_fam hodd (by omega) θ hnat
  have hact : ∀ (y : MulAut V) (hy : y ∈ Y) (p : Fin m),
      y (w p) = w ((θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p) := by
    intro y hy p
    have hs : ∀ z ∈ Y, y * z * y⁻¹ ∈ Y := fun z hz => Y.mul_mem (Y.mul_mem hy hz) (Y.inv_mem hy)
    have hs' : ∀ z ∈ Y, y⁻¹ * z * y ∈ Y := fun z hz =>
      Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hz) hy
    refine caw_apply θ hmem hfix huniq hs hs' (π := (θ ⟨y, hy⟩ : Equiv.Perm (Fin m))) ?_ p
    intro z hz
    have : (⟨y * z * y⁻¹, hs z hz⟩ : ↥Y) = ⟨y, hy⟩ * ⟨z, hz⟩ * ⟨y, hy⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    rfl
  have hperm : ∀ σ : alternatingGroup (Fin m), ∃ y : MulAut V, ∀ r : Fin m,
      y (w r) = w ((σ : Equiv.Perm (Fin m)) r) := by
    intro σ
    refine ⟨(θ.symm σ : MulAut V), fun r => ?_⟩
    rw [hact _ (θ.symm σ).2 r]
    have : θ ⟨(θ.symm σ : MulAut V), (θ.symm σ).2⟩ = σ := θ.apply_symm_apply σ
    rw [this]
  have hinj : Function.Injective w := by
    intro p q hpq
    by_contra hne
    have hconst : ∀ r, w r = w p := by
      intro r
      by_cases hrp : r = p
      · rw [hrp]
      obtain ⟨σ, hσF, hσq⟩ := caw_exists_perm hm (F := {p}) (by simp) (i := q) (j := r)
        (by simpa using Ne.symm hne) (by simpa using hrp)
      obtain ⟨y, hy⟩ := hperm σ
      have hσp : (σ : Equiv.Perm (Fin m)) p = p := hσF p (Finset.mem_singleton_self p)
      have h1 := hy p
      have h2 := hy q
      rw [hσp] at h1
      rw [hσq, ← hpq, h1] at h2
      exact h2.symm
    have hef : w p ∈ fixV Y := by
      intro y hy
      rw [hact y hy p]
      exact hconst _
    have h1 : w p ∈ commV Y ⊓ fixV Y := ⟨(hmem p).1, hef⟩
    rw [commV_inf_fixV_of_natural hodd (by omega) θ hnat] at h1
    exact (hmem p).2 (Subgroup.mem_bot.mp h1)
  refine ⟨w, hmem, hinj, hact, ?_, huniq, ?_⟩
  ·
    have hle : Subgroup.closure (Set.range w) ≤ commV Y := by
      rw [Subgroup.closure_le]
      rintro _ ⟨p, rfl⟩
      exact (hmem p).1
    have hinv : ∀ x ∈ Y, ∀ a ∈ Subgroup.closure (Set.range w),
        (x : MulAut V) a ∈ Subgroup.closure (Set.range w) := by
      intro x hx a ha
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨p, rfl⟩ := ha
        rw [hact x hx p]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      | one => simp
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
      | inv a _ ha => rw [map_inv]; exact inv_mem ha
    rcases commV_subgroup_eq_bot_or_top_of_natural hodd (by omega) θ hnat hinv hle with h0 | h1
    · exfalso
      have hp : w ⟨0, by omega⟩ ∈ Subgroup.closure (Set.range w) := Subgroup.subset_closure ⟨_, rfl⟩
      rw [h0, Subgroup.mem_bot] at hp
      exact (hmem _).2 hp
    · exact h1
  ·
    intro p q p' q' hpq hpp' hpq' hqp' hqq' hp'q' h
    obtain ⟨x, hx⟩ : ∃ x : Fin m, x ∉ ({p, q, p', q'} : Finset (Fin m)) :=
      caw_exists_off (lt_of_le_of_lt Finset.card_le_four (by omega))
    have hF : ({p, q, p'} : Finset (Fin m)).card ≤ 3 := Finset.card_le_three
    have hq' : q' ∉ ({p, q, p'} : Finset (Fin m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hpq', Ne.symm hqq', Ne.symm hp'q'⟩
    have hx' : x ∉ ({p, q, p'} : Finset (Fin m)) := fun hmem' => hx (by simp_all)
    obtain ⟨σ, hσF, hσ⟩ := caw_exists_perm hm hF hq' hx'
    obtain ⟨y, hy⟩ := hperm σ
    have e1 := congrArg (fun v => y v) h
    simp only [map_mul, map_one, hy] at e1
    rw [hσF p (by simp), hσF q (by simp), hσF p' (by simp), hσ] at e1
    have e2 : w q' = w x := mul_left_cancel (h.trans e1.symm)
    exact hx (by rw [← hinj e2]; simp)

theorem wfam_apply_normalizer {m : ℕ} {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {w : Fin m → V}
    (hmem : ∀ p, w p ∈ commV Y ∧ w p ≠ 1)
    (hact : ∀ (y : MulAut V) (hy : y ∈ Y) (p : Fin m),
      y (w p) = w ((θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p))
    (huniq : ∀ (p : Fin m) (u : V), u ∈ commV Y →
      (∀ (y : MulAut V) (hy : y ∈ Y), (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p → y u = u) →
      u = 1 ∨ u = w p)
    {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hs' : ∀ y ∈ Y, s⁻¹ * y * s ∈ Y)
    {π : Equiv.Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Equiv.Perm (Fin m)) =
        π * (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) * π⁻¹) (p : Fin m) :
    s (w p) = w (π p) :=
  caw_apply θ hmem (fun p y hy h => by rw [hact y hy p, h]) huniq hs hs' hπ p

end CFSG.CGT.PushingUpLit.CGT6

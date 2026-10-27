module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

open Subgroup

variable {G X : Type*} [Group G] [Group X]

theorem exists_ext_two {K H : Subgroup G} {e : G} (heH : e ∉ H)
    (hK : ∀ x ∈ K, x ∈ H ∨ e⁻¹ * x ∈ H) (he2 : e * e ∈ H) (hn : ∀ h ∈ H, e * h * e⁻¹ ∈ H)
    (f : G → X) (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b) (q : X)
    (hq : q * q = f (e * e)) (hqc : ∀ h ∈ H, q * f h * q⁻¹ = f (e * h * e⁻¹)) :
    ∃ F : G → X, (∀ a ∈ K, ∀ b ∈ K, F (a * b) = F a * F b) ∧ (∀ h ∈ H, F h = f h) ∧
      F e = q := by
  classical
  have hf1 : f 1 = 1 := by
    have h := hf 1 (one_mem H) 1 (one_mem H)
    rw [one_mul] at h
    exact (mul_eq_left.mp h.symm)
  have hn' : ∀ h ∈ H, e⁻¹ * h * e ∈ H := by
    intro h hh
    have h1 : e⁻¹ * h * e = (e * e)⁻¹ * (e * h * e⁻¹) * (e * e) := by group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem he2) (hn h hh)) he2
  have hqc' : ∀ h ∈ H, f (e⁻¹ * h * e) = q⁻¹ * f h * q := by
    intro h hh
    have := hqc _ (hn' h hh)
    rw [show e * (e⁻¹ * h * e) * e⁻¹ = h by group] at this
    rw [← this]
    group
  set F : G → X := fun x => if x ∈ H then f x else q * f (e⁻¹ * x) with hF
  have hFH : ∀ x ∈ H, F x = f x := fun x hx => by simp [hF, hx]
  have hFnH : ∀ x, x ∉ H → F x = q * f (e⁻¹ * x) := fun x hx => by simp [hF, hx]
  refine ⟨F, ?_, hFH, ?_⟩
  · intro a ha b hb
    rcases hK a ha with haH | haH <;> rcases hK b hb with hbH | hbH
    · rw [hFH _ (mul_mem haH hbH), hFH _ haH, hFH _ hbH, hf _ haH _ hbH]
    · by_cases hb' : b ∈ H
      · rw [hFH _ (mul_mem haH hb'), hFH _ haH, hFH _ hb', hf _ haH _ hb']
      have hab : a * b ∉ H := fun h => hb' (by
        have := mul_mem (inv_mem haH) h
        rwa [inv_mul_cancel_left] at this)
      rw [hFnH _ hab, hFH _ haH, hFnH _ hb']
      have h1 : e⁻¹ * (a * b) = (e⁻¹ * a * e) * (e⁻¹ * b) := by group
      rw [h1, hf _ (hn' a haH) _ hbH, hqc' a haH]
      group
    · by_cases ha' : a ∈ H
      · rw [hFH _ (mul_mem ha' hbH), hFH _ ha', hFH _ hbH, hf _ ha' _ hbH]
      have hab : a * b ∉ H := fun h => ha' (by
        have := mul_mem h (inv_mem hbH)
        rwa [mul_inv_cancel_right] at this)
      rw [hFnH _ hab, hFnH _ ha', hFH _ hbH]
      have h1 : e⁻¹ * (a * b) = (e⁻¹ * a) * b := by group
      rw [h1, hf _ haH _ hbH, mul_assoc]
    · by_cases ha' : a ∈ H
      · by_cases hb' : b ∈ H
        · rw [hFH _ (mul_mem ha' hb'), hFH _ ha', hFH _ hb', hf _ ha' _ hb']
        · have hab : a * b ∉ H := fun h => hb' (by
            have := mul_mem (inv_mem ha') h
            rwa [inv_mul_cancel_left] at this)
          rw [hFnH _ hab, hFH _ ha', hFnH _ hb']
          have h1 : e⁻¹ * (a * b) = (e⁻¹ * a * e) * (e⁻¹ * b) := by group
          rw [h1, hf _ (hn' a ha') _ hbH, hqc' a ha']
          group
      · by_cases hb' : b ∈ H
        · have hab : a * b ∉ H := fun h => ha' (by
            have := mul_mem h (inv_mem hb')
            rwa [mul_inv_cancel_right] at this)
          rw [hFnH _ hab, hFnH _ ha', hFH _ hb']
          have h1 : e⁻¹ * (a * b) = (e⁻¹ * a) * b := by group
          rw [h1, hf _ haH _ hb', mul_assoc]
        ·
          have hmem : (e * e) * (e⁻¹ * (e⁻¹ * a) * e) * (e⁻¹ * b) ∈ H :=
            mul_mem (mul_mem he2 (hn' _ haH)) hbH
          have h1 : a * b = (e * e) * (e⁻¹ * (e⁻¹ * a) * e) * (e⁻¹ * b) := by group
          rw [h1, hFH _ hmem, hf _ (mul_mem he2 (hn' _ haH)) _ hbH, hf _ he2 _ (hn' _ haH),
            hqc' _ haH, ← hq, hFnH _ ha', hFnH _ hb']
          group
  · rw [hFnH _ heH, inv_mul_cancel, hf1, mul_one]

theorem mem_or_mem_of_mem_sup {H : Subgroup G} {e : G} (he2 : e * e ∈ H)
    (hn : ∀ h ∈ H, e * h * e⁻¹ ∈ H) {x : G} (hx : x ∈ H ⊔ zpowers e) :
    x ∈ H ∨ e⁻¹ * x ∈ H := by
  have hn' : ∀ h ∈ H, e⁻¹ * h * e ∈ H := by
    intro h hh
    have h1 : e⁻¹ * h * e = (e * e)⁻¹ * (e * h * e⁻¹) * (e * e) := by group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem he2) (hn h hh)) he2
  let S : Subgroup G :=
    { carrier := {x | x ∈ H ∨ e⁻¹ * x ∈ H}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · right
          have : e⁻¹ * (a * b) = (e⁻¹ * a * e) * (e⁻¹ * b) := by group
          rw [this]
          exact mul_mem (hn' a ha) hb
        · right
          have : e⁻¹ * (a * b) = (e⁻¹ * a) * b := by group
          rw [this]
          exact mul_mem ha hb
        · left
          have : a * b = (e * e) * (e⁻¹ * (e⁻¹ * a) * e) * (e⁻¹ * b) := by group
          rw [this]
          exact mul_mem (mul_mem he2 (hn' _ ha)) hb
      one_mem' := Or.inl (one_mem H)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · right
          have h2 : e⁻¹ * a⁻¹ = e⁻¹ * (e⁻¹ * a)⁻¹ * e * (e * e)⁻¹ := by group
          rw [h2]
          exact mul_mem (hn' _ (inv_mem ha)) (inv_mem he2) }
  have hle : H ⊔ zpowers e ≤ S := by
    refine sup_le (fun h hh => Or.inl hh) ?_
    rw [zpowers_le]
    right
    rw [inv_mul_cancel]
    exact one_mem H
  exact hle hx


@[expose] def nfProd {M : Type*} [Monoid M] : List M → List Bool → M
  | g :: gs, b :: bs => (if b then g else 1) * nfProd gs bs
  | _, _ => 1

@[expose] def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).map (false :: ·) ++ (allBits n).map (true :: ·)

theorem nfProd_mem_closure {S : Set G} : ∀ (gs : List G), (∀ g ∈ gs, g ∈ S) → ∀ bs,
    nfProd gs bs ∈ closure S
  | [], _, _ => by simp [nfProd, one_mem]
  | g :: gs, h, [] => by simp [nfProd, one_mem]
  | g :: gs, h, b :: bs => by
    have hg : g ∈ closure S := subset_closure (h g (List.mem_cons_self))
    have := nfProd_mem_closure gs (fun x hx => h x (List.mem_cons_of_mem _ hx)) bs
    cases b
    · simpa [nfProd] using this
    · simpa [nfProd] using mul_mem hg this

@[expose] def PcRel : List (G × X) → Prop
  | [] => True
  | (g, p) :: L =>
    (∃ bs, g * g = nfProd (L.map Prod.fst) bs ∧ p * p = nfProd (L.map Prod.snd) bs) ∧
    (∀ r ∈ L, ∃ bs, g * r.1 * g⁻¹ = nfProd (L.map Prod.fst) bs ∧
      p * r.2 * p⁻¹ = nfProd (L.map Prod.snd) bs) ∧
    (∀ bs ∈ allBits L.length, g ≠ nfProd (L.map Prod.fst) bs) ∧
    PcRel L

theorem exists_of_pcRel : ∀ L : List (G × X), PcRel L →
    ∃ F : G → X,
      (∀ a ∈ closure {x | x ∈ L.map Prod.fst}, ∀ b ∈ closure {x | x ∈ L.map Prod.fst},
        F (a * b) = F a * F b) ∧
      (∀ r ∈ L, F r.1 = r.2) ∧
      (∀ bs, F (nfProd (L.map Prod.fst) bs) = nfProd (L.map Prod.snd) bs) ∧
      (∀ x ∈ closure {x | x ∈ L.map Prod.fst}, ∃ bs ∈ allBits L.length,
        x = nfProd (L.map Prod.fst) bs)
  | [], _ => by
    refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
    · intro a _ b _
      simp
    · simp
    · intro bs
      simp [nfProd]
    · intro x hx
      have : x = 1 := by simpa using hx
      exact ⟨[], by simp [allBits], by simp [this, nfProd]⟩
  | (g, p) :: L, ⟨⟨bs2, hg2, hp2⟩, hconj, hnot, hL⟩ => by
    classical
    obtain ⟨F₀, hF₀m, hF₀r, hF₀nf, hcoll⟩ := exists_of_pcRel L hL
    set H : Subgroup G := closure {x | x ∈ L.map Prod.fst} with hH
    have hnfH : ∀ bs, nfProd (L.map Prod.fst) bs ∈ H :=
      nfProd_mem_closure _ (fun x hx => hx)
    have hF₀1 : F₀ 1 = 1 := by
      have h := hF₀m 1 (one_mem H) 1 (one_mem H)
      rw [one_mul] at h
      exact (mul_eq_left.mp h.symm)
    have hF₀inv : ∀ a ∈ H, F₀ a⁻¹ = (F₀ a)⁻¹ := by
      intro a ha
      have h := hF₀m a⁻¹ (inv_mem ha) a ha
      rw [inv_mul_cancel, hF₀1] at h
      exact eq_inv_of_mul_eq_one_left h.symm
    have hn : ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
      intro h hh
      induction hh using closure_induction with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
        obtain ⟨bs, h1, -⟩ := hconj r hr
        rw [h1]
        exact hnfH bs
      | one => simp [one_mem]
      | mul a b _ _ ha hb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact mul_mem ha hb
      | inv a _ ha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem ha
    have hg2H : g * g ∈ H := by rw [hg2]; exact hnfH bs2
    have hgH : g ∉ H := by
      intro hgH
      obtain ⟨bs, hbs, hg⟩ := hcoll g hgH
      exact hnot bs hbs hg
    have hq : p * p = F₀ (g * g) := by rw [hg2, hF₀nf, hp2]
    have hqc : ∀ h ∈ H, p * F₀ h * p⁻¹ = F₀ (g * h * g⁻¹) := by
      intro h hh
      induction hh using closure_induction with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
        obtain ⟨bs, h1, h2⟩ := hconj r hr
        rw [hF₀r r hr, h2, h1, hF₀nf]
      | one => simp [hF₀1]
      | mul a b ha hb iha ihb =>
        rw [hF₀m a ha b hb]
        have e1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e1, hF₀m _ (hn a ha) _ (hn b hb), ← iha, ← ihb]
        group
      | inv a ha iha =>
        rw [hF₀inv a ha]
        have e1 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e1, hF₀inv _ (hn a ha), ← iha]
        group
    have hK : closure {x | x ∈ ((g, p) :: L).map Prod.fst} = H ⊔ zpowers g := by
      rw [hH, zpowers_eq_closure, ← Subgroup.closure_union]
      congr 1
      ext x
      simp
    obtain ⟨F, hFm, hFH, hFg⟩ := exists_ext_two (K := H ⊔ zpowers g) hgH
      (fun x hx => mem_or_mem_of_mem_sup hg2H hn hx) hg2H hn F₀ hF₀m p hq hqc
    rw [hK]
    have hHK : H ≤ H ⊔ zpowers g := le_sup_left
    have hgK : g ∈ H ⊔ zpowers g := le_sup_right (a := H) (mem_zpowers g)
    refine ⟨F, hFm, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hFg
      · rw [hFH _ (subset_closure (List.mem_map.mpr ⟨r, hr, rfl⟩)), hF₀r r hr]
    · intro bs
      cases bs with
      | nil =>
        simp only [List.map_cons, nfProd]
        rw [hFH 1 (one_mem H), hF₀1]
      | cons b bs =>
        cases b
        · simp only [nfProd, List.map_cons, Bool.false_eq_true, ↓reduceIte, one_mul]
          rw [hFH _ (hnfH bs), hF₀nf]
        · simp only [nfProd, List.map_cons, ↓reduceIte]
          rw [hFm g hgK _ (hHK (hnfH bs)), hFg, hFH _ (hnfH bs), hF₀nf]
    · intro x hx
      rcases mem_or_mem_of_mem_sup hg2H hn hx with hxH | hxH
      · obtain ⟨bs, hbs, rfl⟩ := hcoll x hxH
        refine ⟨false :: bs, ?_, by simp [nfProd]⟩
        simp only [List.length_cons, allBits, List.mem_append, List.mem_map]
        exact Or.inl ⟨bs, hbs, rfl⟩
      · obtain ⟨bs, hbs, hx'⟩ := hcoll _ hxH
        refine ⟨true :: bs, ?_, ?_⟩
        · simp only [List.length_cons, allBits, List.mem_append, List.mem_map]
          exact Or.inr ⟨bs, hbs, rfl⟩
        · simp only [nfProd, List.map_cons, ↓reduceIte]
          rw [← hx']
          group

theorem exists_hom_of_pcRel (L : List (G × X)) (hL : PcRel L)
    (htop : ∀ x : G, ∃ bs ∈ allBits L.length, x = nfProd (L.map Prod.fst) bs) :
    ∃ F : G →* X, (∀ r ∈ L, F r.1 = r.2) ∧
      ∀ bs, F (nfProd (L.map Prod.fst) bs) = nfProd (L.map Prod.snd) bs := by
  obtain ⟨F, hFm, hFr, hFnf, -⟩ := exists_of_pcRel L hL
  have hall : ∀ x : G, x ∈ closure {x | x ∈ L.map Prod.fst} := by
    intro x
    obtain ⟨bs, -, rfl⟩ := htop x
    exact nfProd_mem_closure _ (fun x hx => hx) bs
  have hF1 : F 1 = 1 := by
    have h := hFm 1 (hall 1) 1 (hall 1)
    rw [one_mul] at h
    exact (mul_eq_left.mp h.symm)
  exact ⟨⟨⟨F, hF1⟩, fun a b => hFm a (hall a) b (hall b)⟩, hFr, hFnf⟩

theorem mem_allBits : ∀ bs : List Bool, bs ∈ allBits bs.length
  | [] => by simp [allBits]
  | b :: bs => by
    simp only [List.length_cons, allBits, List.mem_append, List.mem_map]
    cases b
    · exact Or.inl ⟨bs, mem_allBits bs, rfl⟩
    · exact Or.inr ⟨bs, mem_allBits bs, rfl⟩

theorem map_nfProd {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) :
    ∀ (L : List M) (bs : List Bool), f (nfProd L bs) = nfProd (L.map f) bs
  | [], _ => by simp [nfProd]
  | _ :: _, [] => by simp [nfProd]
  | g :: gs, b :: bs => by
    cases b <;> simp [nfProd, map_nfProd f gs bs]

@[expose] def InSpan (gs : List G) (x : G) : Prop := ∃ bs ∈ allBits gs.length, x = nfProd gs bs

instance [DecidableEq G] (gs : List G) (x : G) : Decidable (InSpan gs x) :=
  inferInstanceAs (Decidable (∃ bs ∈ allBits gs.length, x = nfProd gs bs))

theorem map_mem_of_inSpan {N : Type*} [Group N] (f : G →* N) {gs : List G} {x : G}
    (hx : InSpan gs x) {H : Subgroup N} (hH : ∀ g ∈ gs, f g ∈ H) : f x ∈ H := by
  obtain ⟨bs, -, rfl⟩ := hx
  rw [map_nfProd]
  have h := nfProd_mem_closure (S := (H : Set N)) (gs.map f) (by simpa using hH) bs
  rwa [closure_eq] at h

end CFSG.ComponentClassification.HSFLit.Sec8

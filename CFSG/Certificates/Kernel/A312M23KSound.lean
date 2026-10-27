module

public import Certificates.Data.Kernel.A312M23K
public import CFSG.Certificates.Kernel.A312HeKSound
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core

public section

namespace CFSG.KC.A312M23K

open CFSG.KC.E64F CFSG.KC.A312HeK CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin
  CFSG.Quasithin.A312Words
open scoped Pointwise

@[expose] def Rep {Γ : Type} [Group Γ] (n : ℕ) [MulAction Γ (Fin n)] (T : List (List ℕ)) (l : ℕ)
    (g : Γ) : Prop :=
  ∀ p < n, tf T l p = act n g p

@[expose] noncomputable def el (Γ : Type) [Group Γ] (n : ℕ) [MulAction Γ (Fin n)]
    (T : List (List ℕ)) (l : ℕ) : Γ := by
  classical exact if h : ∃ g : Γ, Rep n T l g then h.choose else 1

@[expose] noncomputable def wp (Γ : Type) [Group Γ] (n : ℕ) [MulAction Γ (Fin n)]
    (T : List (List ℕ)) (w : List ℕ) : Γ :=
  (w.map (el Γ n T)).prod

@[expose] noncomputable def olT (Γ : Type) [Group Γ] (n : ℕ) [MulAction Γ (Fin n)]
    (T : List (List ℕ)) (α r : ℕ) : List Γ :=
  (List.range (2 * r)).map fun i => el Γ n T (α + i)

@[expose] noncomputable def YT (Γ : Type) [Group Γ] (n : ℕ) [MulAction Γ (Fin n)]
    (T : List (List ℕ)) (nL : ℕ) : Subgroup Γ :=
  Subgroup.closure {g | ∃ l < nL, el Γ n T l = g}

@[expose] def VW (β s : ℕ) : List (List ℕ) := (List.range s).map fun i => [β + i]

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] {T : List (List ℕ)}

theorem eq_of_act (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {g k : Γ}
    (e : ∀ p < n, act n g p = act n k p) : g = k := by
  have := hf (k⁻¹ * g) fun p hp => by
    rw [act_mul _ _ hp, e p hp, act_inv_act _ hp]
  exact (inv_mul_eq_one.mp this).symm

theorem el_rep {l : ℕ} (h : ∃ g : Γ, Rep n T l g) : Rep n T l (el Γ n T l) := by
  unfold el
  rw [dif_pos h]
  exact h.choose_spec

theorem el_eq (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {l : ℕ} {g : Γ}
    (h : Rep n T l g) : el Γ n T l = g :=
  eq_of_act hf fun p hp => by rw [← el_rep ⟨g, h⟩ p hp, h p hp]

theorem wordF_prod {f : ℕ → Γ} : ∀ w : List ℕ, (∀ l ∈ w, Rep n T l (f l)) →
    ∀ p < n, wordF (tf T) w p = act n ((w.map f).prod) p
  | [], _, p, hp => by rw [List.map_nil, List.prod_nil, act_one hp]; rfl
  | l :: w, hw, p, hp => by
    have ih := wordF_prod w (fun x hx => hw x (List.mem_cons_of_mem _ hx)) p hp
    change tf T l (wordF (tf T) w p) = _
    rw [ih, hw l List.mem_cons_self _ (act_lt _ hp), List.map_cons, List.prod_cons,
      act_mul _ _ hp]

theorem wordF_wp {w : List ℕ} (hw : ∀ l ∈ w, ∃ g : Γ, Rep n T l g) :
    ∀ p < n, wordF (tf T) w p = act n (wp Γ n T w) p :=
  wordF_prod w fun l hl => el_rep (hw l hl)

theorem wp_nil : wp Γ n T [] = 1 := rfl

theorem wp_single (l : ℕ) : wp Γ n T [l] = el Γ n T l := by simp [wp]

theorem wp_append (u v : List ℕ) : wp Γ n T (u ++ v) = wp Γ n T u * wp Γ n T v := by
  simp [wp]

theorem wp_repW (w : List ℕ) : ∀ k, wp Γ n T (repW k w) = wp Γ n T w ^ k
  | 0 => by simp [repW, wp_nil]
  | k + 1 => by
    change wp Γ n T (w ++ repW k w) = _
    rw [wp_append, wp_repW w k, pow_succ']

theorem wp_subW : ∀ (V : List (List ℕ)) (e : ℕ),
    wp Γ n T (subW V e) = sp (V.map (wp Γ n T)) e
  | [], _ => rfl
  | v :: V, e => by
    change wp Γ n T ((bif Nat.beq (e % 2) 1 then v else []) ++ subW V (e / 2)) = _
    rw [wp_append, wp_subW V (e / 2)]
    simp only [List.map_cons, sp]
    congr 1
    rw [cond_beq_one]
    split_ifs <;> rfl

theorem mem_subW {l : ℕ} : ∀ {V : List (List ℕ)} {e : ℕ}, l ∈ subW V e → ∃ w ∈ V, l ∈ w
  | [], _, h => by simp [subW] at h
  | v :: V, e, h => by
    change l ∈ (bif Nat.beq (e % 2) 1 then v else []) ++ subW V (e / 2) at h
    rcases List.mem_append.mp h with h | h
    · cases hb : Nat.beq (e % 2) 1
      · rw [hb] at h
        simp at h
      · rw [hb] at h
        exact ⟨v, List.mem_cons_self, h⟩
    · obtain ⟨w, hw, hl⟩ := mem_subW h
      exact ⟨w, List.mem_cons_of_mem _ hw, hl⟩

theorem wp_sh (k : ℕ) (w : List ℕ) : wp Γ n T (sh k w) = (w.map fun a => el Γ n T (k + a)).prod := by
  simp [wp, sh, List.map_map, Function.comp_def]

theorem wp_mem (H : Subgroup Γ) {w : List ℕ} (h : ∀ l ∈ w, el Γ n T l ∈ H) : wp Γ n T w ∈ H :=
  H.list_prod_mem fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact h l hl

theorem eqP_iff (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {u v : List ℕ}
    (hu : ∀ l ∈ u, ∃ g : Γ, Rep n T l g) (hv : ∀ l ∈ v, ∃ g : Γ, Rep n T l g) :
    eqP T n u v = true ↔ wp Γ n T u = wp Γ n T v := by
  unfold eqP
  rw [List.all_eq_true]
  constructor
  · intro h
    refine eq_of_act hf fun p hp => ?_
    have := Nat.eq_of_beq_eq_true (h p (List.mem_range.mpr hp))
    rwa [wordF_wp hu p hp, wordF_wp hv p hp] at this
  · intro h p hp
    have hp' := List.mem_range.mp hp
    rw [wordF_wp hu p hp', wordF_wp hv p hp', h]
    exact Nat.beq_refl _

theorem idP_iff (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {u : List ℕ}
    (hu : ∀ l ∈ u, ∃ g : Γ, Rep n T l g) : idP T n u = true ↔ wp Γ n T u = 1 := by
  unfold idP
  rw [List.all_eq_true]
  constructor
  · intro h
    refine eq_of_act hf fun p hp => ?_
    have := Nat.eq_of_beq_eq_true (h p (List.mem_range.mpr hp))
    rw [wordF_wp hu p hp] at this
    rw [this, act_one hp]
  · intro h p hp
    have hp' := List.mem_range.mp hp
    rw [wordF_wp hu p hp', h, act_one hp']
    exact Nat.beq_refl _

theorem rep_of_eqP {N : ℕ} {w : List ℕ} (hw : ∀ l ∈ w, ∃ g : Γ, Rep n T l g)
    (h : eqP T n [N] w = true) : Rep n T N (wp Γ n T w) := by
  unfold eqP at h
  rw [List.all_eq_true] at h
  intro p hp
  have := Nat.eq_of_beq_eq_true (h p (List.mem_range.mpr hp))
  rw [wordF_wp hw p hp] at this
  exact this

theorem rep_inv {a b : ℕ} {g : Γ} (hb : Rep n T b g) (h : idP T n [a, b] = true) :
    Rep n T a g⁻¹ := by
  unfold idP at h
  rw [List.all_eq_true] at h
  intro q hq
  have hq' := act_lt g⁻¹ hq
  have e := Nat.eq_of_beq_eq_true (h _ (List.mem_range.mpr hq'))
  change tf T a (tf T b (act n g⁻¹ q)) = act n g⁻¹ q at e
  rw [hb _ hq', ← act_mul _ _ hq, mul_inv_cancel, act_one hq] at e
  exact e

theorem let_sound {AB S gw : List (List ℕ)} {sE ab : ℕ → Γ}
    (hS : ∀ i < S.length, Rep n S i (sE i)) (hAB : ∀ i < AB.length, Rep n AB i (ab i))
    (hc : letChk T AB S gw n = true) :
    (∀ i < S.length, Rep n T i (sE i)) ∧
      ∀ g < gw.length, Rep n T (S.length + g) (((gw.getD g []).map ab).prod) := by
  simp only [letChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨fun i hi p hp => ?_, fun g hg p hp => ?_⟩
  · rw [← hS i hi p hp]
    exact Nat.eq_of_beq_eq_true (h1 i hi p hp)
  · rw [Nat.eq_of_beq_eq_true (h3 g hg p hp)]
    exact wordF_prod _ (fun l hl => hAB l (getD_bnd (fun w hw => bnd_iff.mp (h2 w hw)) g l hl))
      p hp

theorem olT_append (α r : ℕ) :
    olT Γ n T α r ++ [el Γ n T (α + 2 * r)] =
      (List.range (2 * r + 1)).map fun a => el Γ n T (α + a) := by
  rw [olT, List.range_succ, List.map_append]
  rfl

theorem mem_olT {α r : ℕ} {g : Γ} : g ∈ olT Γ n T α r ↔ ∃ i < 2 * r, el Γ n T (α + i) = g := by
  simp [olT]

theorem alph_sound (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {nL : ℕ}
    {xs : List (List ℕ × ℕ × ℕ)} {t : List ℕ × ℕ × ℕ} {ws : List (List ℕ)}
    (hL : ∀ l < nL, ∃ g : Γ, Rep n T l g) (hc : alphChk T n nL xs t ws = true) :
    (∀ a < 2 * xs.length + 1, ∃ g : Γ, Rep n T (nL + a) g) ∧
      IdxTwoData (YT Γ n T nL) (olT Γ n T nL xs.length) (el Γ n T (nL + 2 * xs.length)) ∧
      ∀ i < xs.length, el Γ n T (nL + xs.length + i) = (el Γ n T (nL + i))⁻¹ := by
  simp only [alphChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, -⟩, hF⟩, hG⟩ := hc
  set r := xs.length with hr
  have hlet : ∀ w : List ℕ, (∀ l ∈ w, l < nL) → ∀ l ∈ w, ∃ g : Γ, Rep n T l g :=
    fun w hw l hl => hL l (hw l hl)
  have hrepW : ∀ w : List ℕ, (∀ l ∈ w, l < nL) → ∀ k, ∀ l ∈ repW k w, ∃ g : Γ, Rep n T l g :=
    fun w hw k l hl => hL l (hw l (mem_repW hl))
  have hYw : ∀ w : List ℕ, (∀ l ∈ w, l < nL) → wp Γ n T w ∈ YT Γ n T nL := fun w hw =>
    wp_mem _ fun l hl => Subgroup.subset_closure ⟨l, hw l hl, rfl⟩
  have hx : ∀ i < r, Rep n T (nL + i)
      (wp Γ n T (repW (xs.getD i ([], 0, 0)).2.1 (xs.getD i ([], 0, 0)).1)) := fun i hi =>
    rep_of_eqP (hrepW _ (bnd_iff.mp (hA i hi).1.1.1.1) _) (hA i hi).1.1.1.2
  have hxe : ∀ i < r, el Γ n T (nL + i) =
      wp Γ n T (xs.getD i ([], 0, 0)).1 ^ (xs.getD i ([], 0, 0)).2.1 := fun i hi => by
    rw [el_eq hf (hx i hi), wp_repW]
  have hxY : ∀ i < r, el Γ n T (nL + i) ∈ YT Γ n T nL := fun i hi => by
    rw [hxe i hi]
    exact pow_mem (hYw _ (bnd_iff.mp (hA i hi).1.1.1.1)) _
  have hxi : ∀ i < r, Rep n T (nL + r + i) (el Γ n T (nL + i))⁻¹ := fun i hi =>
    rep_inv (el_rep ⟨_, hx i hi⟩) (hA i hi).1.1.2
  have hxie : ∀ i < r, el Γ n T (nL + r + i) = (el Γ n T (nL + i))⁻¹ := fun i hi =>
    el_eq hf (hxi i hi)
  have hodd : ∀ i < r, (xs.getD i ([], 0, 0)).2.2 % 2 = 1 ∧
      el Γ n T (nL + i) ^ (xs.getD i ([], 0, 0)).2.2 = 1 := fun i hi => by
    refine ⟨Nat.eq_of_beq_eq_true (hA i hi).1.2, ?_⟩
    have h1 := (idP_iff hf (fun l hl => ?_)).mp (hA i hi).2
    · rwa [wp_repW, wp_single] at h1
    · have := mem_repW hl
      simp only [List.mem_singleton] at this
      exact ⟨_, this ▸ hx i hi⟩
  have ht : Rep n T (nL + 2 * r) (wp Γ n T (repW t.2.1 t.1)) :=
    rep_of_eqP (hrepW _ (bnd_iff.mp hB) _) hC
  have hte : el Γ n T (nL + 2 * r) = wp Γ n T t.1 ^ t.2.1 := by rw [el_eq hf ht, wp_repW]
  have hrep : ∀ a < 2 * r + 1, ∃ g : Γ, Rep n T (nL + a) g := by
    intro a ha
    rcases lt_or_ge a r with h1 | h1
    · exact ⟨_, hx a h1⟩
    rcases lt_or_ge a (2 * r) with h2 | h2
    · obtain ⟨i, rfl⟩ : ∃ i, a = r + i := ⟨a - r, by omega⟩
      rw [← Nat.add_assoc]
      exact ⟨_, hxi i (by omega)⟩
    · obtain rfl : a = 2 * r := by omega
      exact ⟨_, ht⟩
  have hol : ∀ i < 2 * r, el Γ n T (nL + i) ∈ YT Γ n T nL := fun i hi => by
    rcases lt_or_ge i r with h1 | h1
    · exact hxY i h1
    · obtain ⟨k, rfl⟩ : ∃ k, i = r + k := ⟨i - r, by omega⟩
      rw [← Nat.add_assoc, hxie k (by omega)]
      exact inv_mem (hxY k (by omega))
  refine ⟨hrep, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun i hi => hxie i hi⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := mem_olT.mp hg
    exact hol i hi
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := mem_olT.mp hg
    rcases lt_or_ge i r with h1 | h1
    · exact ⟨_, hodd i h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = r + k := ⟨i - r, by omega⟩
      rw [← Nat.add_assoc, hxie k (by omega)]
      exact ⟨_, (hodd k (by omega)).1, by rw [inv_pow, (hodd k (by omega)).2, inv_one]⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := mem_olT.mp hg
    rcases lt_or_ge i r with h1 | h1
    · refine mem_olT.mpr ⟨r + i, by omega, ?_⟩
      rw [← Nat.add_assoc, hxie i h1]
    · obtain ⟨k, rfl⟩ : ∃ k, i = r + k := ⟨i - r, by omega⟩
      refine mem_olT.mpr ⟨k, by omega, ?_⟩
      rw [← Nat.add_assoc, hxie k (by omega), inv_inv]
  · rw [hte]
    exact pow_mem (hYw _ (bnd_iff.mp hB)) _
  · have h1 := (idP_iff hf (u := [nL + 2 * r, nL + 2 * r]) (fun l hl => ?_)).mp hD
    · simpa [wp] using h1
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_self] at hl
      exact ⟨_, hl ▸ ht⟩
  · rw [YT, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hwl : ∀ a ∈ ws.getD l [], a < 2 * r + 1 :=
      getD_bnd (fun w hw => bnd_iff.mp (hF w hw)) l
    have hsh : ∀ x ∈ sh nL (ws.getD l []), ∃ g : Γ, Rep n T x g := by
      intro x hx
      simp only [sh, List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hrep a (hwl a ha)
    have e := (eqP_iff hf (u := [l]) (fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hL l hl) hsh).mp (hG l hl)
    rw [wp_single] at e
    change el Γ n T l ∈ Subgroup.closure {g | g ∈ olT Γ n T nL r ++ [el Γ n T (nL + 2 * r)]}
    rw [e, wp_sh, olT_append]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (List.mem_map.mpr ⟨a, List.mem_range.mpr (hwl a ha), rfl⟩)

theorem vdata_sound (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {α r β : ℕ}
    (hA : ∀ a < 2 * r + 1, ∃ g : Γ, Rep n T (α + a) g) {vws : List (List ℕ)} {wit ex : List ℕ}
    (hb : vws.all (bnd (2 * r)) = true)
    (heq : ∀ i < vws.length, eqP T n [β + i] (sh α (vws.getD i [])) = true)
    (hci : commInv (tf T) (List.range n) (VW β vws.length) = true)
    (hwit : witChk (tf T) (List.range n) (VW β vws.length) wit = true)
    (hnorm : ∀ a < 2 * r + 1,
      normA (tf T) (List.range n) (VW α (2 * r + 1)) (VW β vws.length) ex a = true) :
    let vl := (List.range vws.length).map fun i => el Γ n T (β + i)
    (∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ olT Γ n T α r}) ∧
      (∀ g ∈ olT Γ n T α r ++ [el Γ n T (α + 2 * r)], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
        g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl}) ∧
      (∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a) ∧ (∀ a ∈ vl, a * a = 1) ∧
      Nat.card (Subgroup.closure {v | v ∈ vl}) = 2 ^ vws.length := by
  intro vl
  rw [List.all_eq_true] at hb
  have hvb : ∀ i, ∀ a ∈ vws.getD i [], a < 2 * r := getD_bnd fun w hw => bnd_iff.mp (hb w hw)
  have hvr : ∀ i < vws.length, Rep n T (β + i) (wp Γ n T (sh α (vws.getD i []))) := by
    intro i hi
    refine rep_of_eqP (fun x hx => ?_) (heq i hi)
    simp only [sh, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hA a (by have := hvb i a ha; omega)
  have hVok : ∀ w ∈ VW β vws.length, ∀ l ∈ w, ∃ g : Γ, Rep n T l g := by
    intro w hw l hl
    simp only [VW, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    rw [List.mem_singleton.mp hl]
    exact ⟨_, hvr i hi⟩
  have hAok : ∀ w ∈ VW α (2 * r + 1), ∀ l ∈ w, ∃ g : Γ, Rep n T l g := by
    intro w hw l hl
    simp only [VW, List.mem_map, List.mem_range] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [List.mem_singleton.mp hl]
    exact hA a ha
  have hVm : (VW β vws.length).map (wp Γ n T) = vl := by
    simp [VW, vl, wp_single, Function.comp_def]
  have hAm : (VW α (2 * r + 1)).map (wp Γ n T) = olT Γ n T α r ++ [el Γ n T (α + 2 * r)] := by
    rw [olT_append]
    simp [VW, wp_single, Function.comp_def]
  have hgetV : ∀ i < vws.length, (VW β vws.length).getD i [] = [β + i] := fun i hi => by
    simp [VW, List.getD_eq_getElem?_getD, hi]
  have hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {g | g ∈ olT Γ n T α r} := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hi
    rw [el_eq hf (hvr i hi), wp_sh]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (mem_olT.mpr ⟨a, hvb i a ha, rfl⟩)
  unfold commInv at hci
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hci
  obtain ⟨hsqc, hcc⟩ := hci
  have happ : ∀ u v : List ℕ, (∀ l ∈ u, ∃ g : Γ, Rep n T l g) → (∀ l ∈ v, ∃ g : Γ, Rep n T l g) →
      ∀ l ∈ u ++ v, ∃ g : Γ, Rep n T l g := fun u v hu hv l hl => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hu l hl
    · exact hv l hl
  have hgetok : ∀ i, ∀ l ∈ (VW β vws.length).getD i [], ∃ g : Γ, Rep n T l g := by
    intro i l hl
    by_cases hi : i < (VW β vws.length).length
    · rw [List.getD_eq_getElem _ _ hi] at hl
      exact hVok _ (List.getElem_mem _) l hl
    · rw [List.getD_eq_default _ _ (by omega)] at hl
      simp at hl
  have hvsq : ∀ a ∈ vl, a * a = 1 := by
    intro a ha
    rw [← hVm] at ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    have := (idP_iff hf (happ _ _ (hVok w hw) (hVok w hw))).mp (hsqc w hw)
    rwa [wp_append] at this
  have hvc : ∀ a ∈ vl, ∀ b ∈ vl, a * b = b * a := by
    have hlen : vl.length = (VW β vws.length).length := by simp [vl, VW]
    have hget : ∀ i (hi : i < vl.length),
        vl[i] = wp Γ n T ((VW β vws.length).getD i []) := fun i hi => by
      have hi' : i < vws.length := by simpa [vl] using hi
      rw [hgetV i hi', wp_single]
      simp [vl]
    have key : ∀ i (hi : i < vl.length) k (hk : k < i), vl[i] * vl[k] = vl[k] * vl[i] := by
      intro i hi k hk
      have hi' : i < (VW β vws.length).length := by rw [← hlen]; exact hi
      have e := (eqP_iff hf (happ _ _ (hgetok i) (hgetok k)) (happ _ _ (hgetok k) (hgetok i))).mp
        (hcc i hi' k hk)
      rw [wp_append, wp_append] at e
      rw [hget i hi, hget k (by omega)]
      exact e
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    rcases lt_trichotomy k i with hki | rfl | hik
    · exact key i hi k hki
    · rfl
    · exact (key k hk i hik).symm
  have hne : ∀ e, 0 < e → e < 2 ^ vl.length → sp vl e ≠ 1 := by
    intro e he0 he1 hsp
    have hlen : vl.length = (VW β vws.length).length := by simp [vl, VW]
    unfold witChk at hwit
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hwit
    obtain ⟨hwl, hall⟩ := hwit
    have hwl' := Nat.eq_of_beq_eq_true hwl
    obtain ⟨hlt, hmv⟩ := hall (e - 1) (by rw [hwl']; rw [hlen] at he1; omega)
    rw [Nat.sub_add_cancel he0] at hmv
    have hq : (List.range n).getD (wit.getD (e - 1) 0) 0 < n := by
      have := Nat.blt_eq.mp hlt
      rw [List.length_range] at this
      rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact this), List.getElem_range]
      exact this
    have hsub : ∀ l ∈ subW (VW β vws.length) e, ∃ g : Γ, Rep n T l g := fun l hl => by
      obtain ⟨w, hw, hlw⟩ := mem_subW hl
      exact hVok w hw l hlw
    have hfix := wordF_wp hsub _ hq
    rw [wp_subW, hVm, hsp, act_one hq] at hfix
    rw [hfix, Nat.beq_refl] at hmv
    exact absurd hmv (by decide)
  have hVnorm : ∀ g ∈ olT Γ n T α r ++ [el Γ n T (α + 2 * r)], ∀ v ∈ Subgroup.closure {v | v ∈ vl},
      g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ vl} := by
    intro g hg
    rw [olT_append] at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at ha
    refine conj_closure fun v hv => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hi
    have hc := hnorm a ha
    unfold normA at hc
    rw [List.all_eq_true] at hc
    have hci := hc i (List.mem_range.mpr (by simpa [VW] using hi))
    simp only [Bool.and_eq_true] at hci
    have hgetA : (VW α (2 * r + 1)).getD a [] = [α + a] := by
      simp [VW, List.getD_eq_getElem?_getD, ha]
    rw [hgetV i hi, hgetA] at hci
    have hsub : ∀ l ∈ subW (VW β vws.length) (ex.getD ((VW β vws.length).length * a + i) 0),
        ∃ g : Γ, Rep n T l g := fun l hl => by
      obtain ⟨w, hw, hlw⟩ := mem_subW hl
      exact hVok w hw l hlw
    have e := (eqP_iff hf (u := [β + i] ++ [α + a]) (fun l hl => by
        rcases List.mem_append.mp hl with hl | hl <;> rw [List.mem_singleton.mp hl]
        · exact ⟨_, hvr i hi⟩
        · exact hA a ha)
      (happ _ _ (fun l hl => by rw [List.mem_singleton.mp hl]; exact hA a ha) hsub)).mp hci.2
    rw [wp_append, wp_append, wp_single, wp_single, wp_subW, hVm] at e
    have e2 : (el Γ n T (α + a))⁻¹ * el Γ n T (β + i) * el Γ n T (α + a) =
        sp vl (ex.getD ((VW β vws.length).length * a + i) 0) := by
      rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2]
    exact sp_mem _ vl (fun g hg => Subgroup.subset_closure hg) _
  have hcard := card_closure_sp vl hvsq hvc hne
  have hvlen : vl.length = vws.length := by simp [vl]
  rw [hvlen] at hcard
  exact ⟨hvol, hVnorm, hvc, hvsq, hcard⟩

@[expose] def bPt (n : ℕ) (bl : List (List ℕ)) (i : Fin bl.length) : Set (Fin n) :=
  CFSG.Quasithin.A312M23.blkSet n (bl.getD i.1 [])

theorem act_inj {g : Γ} {p q : ℕ} (hp : p < n) (hq : q < n) (h : act n g p = act n g q) :
    p = q := by
  rw [← act_inv_act g hp, h, act_inv_act g hq]

theorem smul_blk_eq {g : Γ} {b b' : List ℕ} (hb : b.Nodup) (hb' : b'.Nodup)
    (hlt : ∀ p ∈ b, p < n) (hlen : b.length = b'.length) (hin : ∀ p ∈ b, act n g p ∈ b') :
    g • CFSG.Quasithin.A312M23.blkSet n b = CFSG.Quasithin.A312M23.blkSet n b' := by
  rw [CFSG.Quasithin.A312M23.smul_blkSet g hlt]
  have hnd : (b.map (act n g)).Nodup :=
    hb.map_on fun x hx y hy hxy => act_inj (hlt x hx) (hlt y hy) hxy
  have hsub : b.map (act n g) ⊆ b' := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hin p hp
  have hperm := (hnd.subperm hsub).perm_of_length_le (by rw [List.length_map, hlen])
  ext x
  exact hperm.mem_iff

theorem blk_sound {bl : List (List ℕ)} {gs : List ℕ} {bi : List (List ℕ)}
    (hg : ∀ k < gs.length, ∃ g : Γ, Rep n T (gs.getD k 0) g)
    (hc : blkChk T n bl gs bi = true) :
    (∀ b ∈ bl, b.Nodup) ∧ (∀ b ∈ bl, ∀ p ∈ b, p < n) ∧
      Function.Injective (bPt n bl) ∧ ∀ k < gs.length, ∀ i : Fin bl.length,
      ∃ hj : (bi.getD k []).getD i.1 0 < bl.length,
        el Γ n T (gs.getD k 0) • bPt n bl i = bPt n bl ⟨_, hj⟩ := by
  simp only [blkChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hne, hsz⟩, hlt⟩, hnd⟩, -⟩, hk⟩ := hc
  have hne' : (bl.headD []).length ≠ 0 := fun h => by
    rw [h, Nat.beq_refl] at hne
    exact absurd hne (by decide)
  have hsz' : ∀ b ∈ bl, b.length = (bl.headD []).length := fun b hb =>
    Nat.eq_of_beq_eq_true (hsz b hb)
  have hlt' : ∀ b ∈ bl, ∀ p ∈ b, p < n := fun b hb p hp =>
    Nat.blt_eq.mp (hlt p (List.mem_flatten.mpr ⟨b, hb, hp⟩))
  obtain ⟨hndb, hpw⟩ := List.nodup_flatten.mp hnd
  have hmem : ∀ i : Fin bl.length, bl.getD i.1 [] ∈ bl := fun i => by
    rw [List.getD_eq_getElem _ _ i.2]
    exact List.getElem_mem _
  refine ⟨hndb, hlt', fun i j hij => ?_, fun k hkl i => ?_⟩
  · have hbi := hmem i
    obtain ⟨p, hp⟩ : ∃ p, p ∈ bl.getD i.1 [] := by
      rcases hl : bl.getD i.1 [] with _ | ⟨p, _⟩
      · have := hsz' _ hbi
        rw [hl] at this
        exact absurd this.symm (by simpa using hne')
      · exact ⟨p, List.mem_cons_self⟩
    have hpn := hlt' _ hbi p hp
    have hpj : (⟨p, hpn⟩ : Fin n) ∈ bPt n bl j := by
      rw [← hij]
      exact hp
    change p ∈ bl.getD j.1 [] at hpj
    by_contra hne2
    have hv : i.1 ≠ j.1 := fun e => hne2 (Fin.ext e)
    rw [List.getD_eq_getElem _ _ i.2] at hp
    rw [List.getD_eq_getElem _ _ j.2] at hpj
    rcases lt_or_gt_of_ne hv with h | h
    · exact (List.pairwise_iff_getElem.mp hpw i.1 j.1 i.2 j.2 h) hp hpj
    · exact (List.pairwise_iff_getElem.mp hpw j.1 i.1 j.2 i.2 h) hpj hp
  · obtain ⟨-, hall⟩ := hk k hkl
    obtain ⟨hj, hin⟩ := hall i.1 i.2
    have hj' := Nat.blt_eq.mp hj
    refine ⟨hj', smul_blk_eq (hndb _ (hmem i)) (hndb _ (hmem ⟨_, hj'⟩)) (hlt' _ (hmem i))
      (by rw [hsz' _ (hmem i), hsz' _ (hmem ⟨_, hj'⟩)]) fun p hp => ?_⟩
    have h1 := hin p hp
    rw [el_rep (hg k hkl) p (hlt' _ (hmem i) p hp)] at h1
    simpa using h1

section Image

open CFSG.Quasithin.A312M23

variable {X : Type} [MulAction Γ X] {m : ℕ}

theorem perm_of_gens {Y : Subgroup Γ} {E : List Γ} (hY : Y ≤ Subgroup.closure {g | g ∈ E})
    (pt : Fin m → X) (hpt : Function.Injective pt) (hE : ∀ g ∈ E, ∀ i, ∃ j, g • pt i = pt j) :
    ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j := by
  have h : Subgroup.closure {g | g ∈ E} ≤ ptStab (Γ := Γ) pt hpt :=
    (Subgroup.closure_le _).mpr fun g hg => mem_ptStab.mpr (hE g hg)
  exact fun z hz => mem_ptStab.mp (h (hY hz))

theorem rho_eq {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {g : Γ} (hg : g ∈ Y) {i j : Fin m}
    (h : g • pt i = pt j) : rhoFn Y pt hpt hYp g i = j :=
  hpt ((rhoFn_spec hg i).symm.trans h)

theorem prod_mem_of {Y : Subgroup Γ} {f : ℕ → Γ} {w : List ℕ} (h : ∀ a ∈ w, f a ∈ Y) :
    (w.map f).prod ∈ Y :=
  Y.list_prod_mem fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha

theorem rho_word {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {bi : List (List ℕ)} {f : ℕ → Γ} :
    ∀ w : List ℕ, (∀ a ∈ w, f a ∈ Y) →
      (∀ a ∈ w, ∀ i : Fin m, (rhoFn Y pt hpt hYp (f a) i).val = tf bi a i.val) →
      ∀ i : Fin m, (rhoFn Y pt hpt hYp (w.map f).prod i).val = wordF (tf bi) w i.val
  | [], _, _, i => by simp [rhoFn_one, wordF]
  | a :: w, hY, hb, i => by
    have hprod : (w.map f).prod ∈ Y := prod_mem_of fun x hx => hY x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.prod_cons, rhoFn_mul (hY a List.mem_cons_self) hprod,
      Equiv.Perm.mul_apply]
    change _ = tf bi a (wordF (tf bi) w i.val)
    rw [← rho_word w (fun x hx => hY x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) i, hb a List.mem_cons_self]

theorem rho_prod_mem {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {E : Subgroup (Equiv.Perm (Fin m))} {f : ℕ → Γ} :
    ∀ w : List ℕ, (∀ a ∈ w, f a ∈ Y) → (∀ a ∈ w, rhoFn Y pt hpt hYp (f a) ∈ E) →
      rhoFn Y pt hpt hYp (w.map f).prod ∈ E
  | [], _, _ => by
    rw [List.map_nil, List.prod_nil, rhoFn_one]
    exact E.one_mem
  | a :: w, hY, hE => by
    rw [List.map_cons, List.prod_cons,
      rhoFn_mul (hY a List.mem_cons_self) (prod_mem_of fun x hx => hY x (List.mem_cons_of_mem _ hx))]
    exact E.mul_mem (hE a List.mem_cons_self)
      (rho_prod_mem w (fun x hx => hY x (List.mem_cons_of_mem _ hx))
        (fun x hx => hE x (List.mem_cons_of_mem _ hx)))

@[expose] def permL (σ : Equiv.Perm (Fin m)) : List ℕ := List.ofFn fun i => (σ i).val

theorem permL_inj {σ τ : Equiv.Perm (Fin m)} (h : permL σ = permL τ) : σ = τ := by
  ext i
  have := congrArg (fun l => l.getD i.1 0) h
  simpa [permL, List.getD_eq_getElem?_getD] using this

theorem permL_mul (σ τ : Equiv.Perm (Fin m)) : permL (σ * τ) = cmp (permL σ) (permL τ) := by
  apply List.ext_getElem (by simp [permL, cmp])
  intro i h1 h2
  simp [permL, cmp, List.getD_eq_getElem?_getD]

theorem bp_eq {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {bi : List (List ℕ)} {f : ℕ → Γ} {w : List ℕ}
    (hY : ∀ a ∈ w, f a ∈ Y)
    (hb : ∀ a ∈ w, ∀ i : Fin m, (rhoFn Y pt hpt hYp (f a) i).val = tf bi a i.val) :
    bp bi m w = permL (rhoFn Y pt hpt hYp (w.map f).prod) := by
  apply List.ext_getElem (by simp [bp, permL])
  intro i h1 h2
  simp only [bp, permL, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact (rho_word w hY hb ⟨i, by simpa [bp] using h1⟩).symm

theorem card_closure_of_closed (F : Finset (Equiv.Perm (Fin m))) (hne : F.Nonempty)
    (hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) :
    Nat.card (Subgroup.closure (F : Set (Equiv.Perm (Fin m)))) = F.card := by
  have hpow : ∀ x ∈ F, ∀ k, x ^ (k + 1) ∈ F := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ ih _ hx
  obtain ⟨x0, hx0⟩ := hne
  have h1 : (1 : Equiv.Perm (Fin m)) ∈ F := by
    have ho := orderOf_pos x0
    have := hpow x0 hx0 (orderOf x0 - 1)
    rwa [Nat.sub_add_cancel ho, pow_orderOf_eq_one] at this
  have hinv : ∀ x ∈ F, x⁻¹ ∈ F := by
    intro x hx
    have ho := orderOf_pos x
    rcases Nat.lt_or_ge 1 (orderOf x) with h | h
    · have e : x⁻¹ = x ^ (orderOf x - 2 + 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, show orderOf x - 2 + 1 + 1 = orderOf x by omega, pow_orderOf_eq_one]
      rw [e]
      exact hpow x hx _
    · have : orderOf x = 1 := by omega
      rw [orderOf_eq_one_iff.mp this, inv_one]
      exact h1
  have hset : (Subgroup.closure (F : Set (Equiv.Perm (Fin m))) : Set (Equiv.Perm (Fin m))) = F := by
    apply le_antisymm
    · intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact hx
      | one => exact h1
      | mul x y _ _ hx hy => exact hmul x hx y hy
      | inv x _ hx => exact hinv x hx
    · exact Subgroup.subset_closure
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem sub_sound {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {E : Subgroup (Equiv.Perm (Fin m))}
    {bi : List (List ℕ)} {f : ℕ → Γ} {nA q : ℕ} {Ws : List (List ℕ)} (hq : 0 < q)
    (hfY : ∀ a < nA, f a ∈ Y) (hfE : ∀ a < nA, rhoFn Y pt hpt hYp (f a) ∈ E)
    (hb : ∀ a < nA, ∀ i : Fin m, (rhoFn Y pt hpt hYp (f a) i).val = tf bi a i.val)
    (hc : subChk bi m nA q Ws = true) : q ∣ Nat.card E := by
  classical
  simp only [subChk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hbnd, hlen⟩, hnd⟩, hcl⟩ := hc
  have hwb : ∀ w ∈ Ws, ∀ a ∈ w, a < nA := fun w hw => bnd_iff.mp (hbnd w hw)
  set P : List ℕ → Equiv.Perm (Fin m) := fun w => rhoFn Y pt hpt hYp (w.map f).prod with hP
  have hbpP : ∀ w ∈ Ws, bp bi m w = permL (P w) := fun w hw =>
    bp_eq (fun a ha => hfY a (hwb w hw a ha)) (fun a ha => hb a (hwb w hw a ha))
  have hmap : Ws.map (bp bi m) = (Ws.map P).map permL := by
    rw [List.map_map]
    exact List.map_congr_left fun w hw => hbpP w hw
  rw [hmap] at hnd hcl
  have hndP : (Ws.map P).Nodup := hnd.of_map _
  set F := (Ws.map P).toFinset with hF
  have hFc : F.card = q := by
    rw [hF, List.toFinset_card_of_nodup hndP, List.length_map, Nat.eq_of_beq_eq_true hlen]
  have hne : F.Nonempty := by
    rw [← Finset.card_pos, hFc]
    exact hq
  have hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F := by
    intro x hx y hy
    rw [hF, List.mem_toFinset] at hx hy ⊢
    have h1 := hcl _ (List.mem_map.mpr ⟨x, hx, rfl⟩) _ (List.mem_map.mpr ⟨y, hy, rfl⟩)
    rw [← permL_mul] at h1
    simp only [List.elem_eq_mem, decide_eq_true_eq, List.mem_map] at h1
    obtain ⟨z, hz, hzl⟩ := h1
    rw [permL_inj hzl] at hz
    exact List.mem_map.mpr hz
  have hle : Subgroup.closure (F : Set (Equiv.Perm (Fin m))) ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Finset.mem_coe, hF, List.mem_toFinset] at hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    exact rho_prod_mem w (fun a ha => hfY a (hwb w hw a ha)) (fun a ha => hfE a (hwb w hw a ha))
  rw [← hFc, ← card_closure_of_closed F hne hmul]
  exact Subgroup.card_dvd_of_le hle

theorem foldr_dvd {N : ℕ} : ∀ spec : List (ℕ × List (List ℕ)),
    (∀ i < spec.length, ∀ k < i,
      Nat.gcd (spec.getD i (0, [])).1 (spec.getD k (0, [])).1 = 1) →
    (∀ s ∈ spec, s.1 ∣ N) → spec.foldr (fun s a => s.1 * a) 1 ∣ N
  | [], _, _ => one_dvd N
  | s :: spec, hco, hd => by
    have ih := foldr_dvd spec (fun i hi k hk => by
      have := hco (i + 1) (by simp; omega) (k + 1) (by omega)
      simpa using this) (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    have hcop : Nat.Coprime s.1 (spec.foldr (fun s a => s.1 * a) 1) := by
      have key : ∀ i < spec.length, Nat.Coprime s.1 (spec.getD i (0, [])).1 := fun i hi => by
        have := hco (i + 1) (by simp; omega) 0 (by omega)
        rw [Nat.gcd_comm] at this
        simpa using this
      clear ih hco hd
      induction spec with
      | nil => exact Nat.coprime_one_right _
      | cons x xs ihx =>
        change Nat.Coprime s.1 (x.1 * xs.foldr (fun s a => s.1 * a) 1)
        refine Nat.Coprime.mul_right (by simpa using key 0 (by simp)) (ihx fun i hi => ?_)
        simpa using key (i + 1) (by simp; omega)
    exact hcop.mul_dvd_of_dvd_of_dvd (hd s List.mem_cons_self) ih

theorem img_sound {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {E : Subgroup (Equiv.Perm (Fin m))}
    {bi : List (List ℕ)} {f : ℕ → Γ} {nA r : ℕ} {spec : List (ℕ × List (List ℕ))} (hr : 0 < r)
    (hfY : ∀ a < nA, f a ∈ Y) (hfE : ∀ a < nA, rhoFn Y pt hpt hYp (f a) ∈ E)
    (hb : ∀ a < nA, ∀ i : Fin m, (rhoFn Y pt hpt hYp (f a) i).val = tf bi a i.val)
    (hc : imgChk bi m nA r spec = true) : r ∣ Nat.card E := by
  simp only [imgChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hprod, hco⟩, hsub⟩ := hc
  have hprod' := Nat.eq_of_beq_eq_true hprod
  have hpos : ∀ s ∈ spec, 0 < s.1 := by
    intro s hs
    have : s.1 ∣ spec.foldr (fun s a => s.1 * a) 1 := by
      clear hprod hprod' hco hsub
      induction spec with
      | nil => simp at hs
      | cons x xs ih =>
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Dvd.intro _ rfl
        · exact Dvd.dvd.mul_left (ih hs) _
    rw [hprod'] at this
    exact Nat.pos_of_dvd_of_pos this hr
  rw [← hprod']
  exact foldr_dvd spec (fun i hi k hk => Nat.eq_of_beq_eq_true (hco i hi k hk))
    fun s hs => sub_sound (hpos s hs) hfY hfE hb (hsub s hs)

theorem cyc_sound {Y : Subgroup Γ} {pt : Fin m → X} {hpt : Function.Injective pt}
    {hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j} {E : Subgroup (Equiv.Perm (Fin m))}
    {bi : List (List ℕ)} {f : ℕ → Γ} {nA : ℕ} {w : List ℕ}
    (hfY : ∀ a < nA, f a ∈ Y) (hfE : ∀ a < nA, rhoFn Y pt hpt hYp (f a) ∈ E)
    (hb : ∀ a < nA, ∀ i : Fin m, (rhoFn Y pt hpt hYp (f a) i).val = tf bi a i.val)
    (hc : cycChk bi m nA w = true) : ∀ i j : Fin m, ∃ e ∈ E, e i = j := by
  simp only [cycChk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at hc
  obtain ⟨hbnd, hall⟩ := hc
  have hwb : ∀ a ∈ w, a < nA := bnd_iff.mp hbnd
  set σ := rhoFn Y pt hpt hYp (w.map f).prod with hσ
  have hσE : σ ∈ E :=
    rho_prod_mem w (fun a ha => hfY a (hwb a ha)) (fun a ha => hfE a (hwb a ha))
  have hbp : bp bi m w = permL σ :=
    bp_eq (fun a ha => hfY a (hwb a ha)) (fun a ha => hb a (hwb a ha))
  have hpw : ∀ k (i : Fin m), pw (permL σ) k i.val = ((σ ^ k) i).val := by
    intro k
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      change (permL σ).getD (pw (permL σ) k i.val) 0 = _
      rw [ih i, pow_succ', Equiv.Perm.mul_apply]
      simp [permL, List.getD_eq_getElem?_getD]
  have hm : ∀ (h0 : 0 < m) (j : Fin m), ∃ e ∈ E, e ⟨0, h0⟩ = j := by
    intro h0 j
    obtain ⟨k, -, hk⟩ := hall j.1 j.2
    rw [hbp] at hk
    have := hpw k ⟨0, h0⟩
    refine ⟨σ ^ k, pow_mem hσE k, Fin.ext ?_⟩
    rw [← this]
    exact Nat.eq_of_beq_eq_true hk
  intro i j
  have h0 : 0 < m := i.pos
  obtain ⟨ei, hei, hi⟩ := hm h0 i
  obtain ⟨ej, hej, hj⟩ := hm h0 j
  refine ⟨ej * ei⁻¹, mul_mem hej (inv_mem hei), ?_⟩
  rw [Equiv.Perm.mul_apply, ← hi]
  simpa using hj

end Image

@[expose] def stabL (n : ℕ) [MulAction Γ (Fin n)] (b : List ℕ) (hb : ∀ p ∈ b, p < n) :
    Subgroup Γ where
  carrier := {g | ∀ p ∈ b, act n g p ∈ b}
  one_mem' := fun p hp => by
    change act n (1 : Γ) p ∈ b
    rw [act_one (hb p hp)]
    exact hp
  mul_mem' := fun {g h} hg hh p hp => by
    change act n (g * h) p ∈ b
    rw [act_mul _ _ (hb p hp)]
    exact hg _ (hh p hp)
  inv_mem' := fun {g} hg p hp => by
    classical
    change act n g⁻¹ p ∈ b
    have hsub : b.toFinset.image (act n g) ⊆ b.toFinset := fun x hx => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact List.mem_toFinset.mpr (hg q (List.mem_toFinset.mp hq))
    have hcard : b.toFinset.card ≤ (b.toFinset.image (act n g)).card := by
      rw [Finset.card_image_of_injOn fun x hx y hy hxy =>
        act_inj (hb x (List.mem_toFinset.mp hx)) (hb y (List.mem_toFinset.mp hy)) hxy]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hp' : p ∈ b.toFinset.image (act n g) := by
      rw [heq]
      exact List.mem_toFinset.mpr hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp'
    rw [act_inv_act g (hb q (List.mem_toFinset.mp hq))]
    exact List.mem_toFinset.mp hq

theorem witB_sound {α r : ℕ} (hA : ∀ a < 2 * r + 1, ∃ g : Γ, Rep n T (α + a) g) {b : List ℕ}
    (hc : witB T n α r b = true) :
    el Γ n T (α + 2 * r) ∉ Subgroup.closure {g | g ∈ olT Γ n T α r} := by
  simp only [witB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    List.all_eq_false] at hc
  obtain ⟨⟨hlt, hodd⟩, ⟨p, hp, hout⟩⟩ := hc
  have hlt' : ∀ p ∈ b, p < n := fun p hp => Nat.blt_eq.mp (hlt p hp)
  have hle : Subgroup.closure {g | g ∈ olT Γ n T α r} ≤ stabL n b hlt' := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨a, ha, rfl⟩ := mem_olT.mp hg
    intro q hq
    have h1 := hodd a ha q hq
    rw [el_rep (hA a (by omega)) q (hlt' q hq)] at h1
    simpa using h1
  intro ht
  have h1 := hle ht p hp
  change act n (el Γ n T (α + 2 * r)) p ∈ b at h1
  rw [← el_rep (hA (2 * r) (by omega)) p (hlt' p hp)] at h1
  simp [h1] at hout

theorem normW_sound (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {α r : ℕ}
    (hA : ∀ a < 2 * r + 1, ∃ g : Γ, Rep n T (α + a) g)
    (ht : el Γ n T (α + 2 * r) * el Γ n T (α + 2 * r) = 1) {wcj : List (List ℕ)}
    (hc : normW T n α r wcj = true) :
    ∀ v ∈ Subgroup.closure {g | g ∈ olT Γ n T α r},
      (el Γ n T (α + 2 * r))⁻¹ * v * el Γ n T (α + 2 * r) ∈
        Subgroup.closure {g | g ∈ olT Γ n T α r} := by
  simp only [normW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨-, hb⟩, he⟩ := hc
  have hti : (el Γ n T (α + 2 * r))⁻¹ = el Γ n T (α + 2 * r) := inv_eq_of_mul_eq_one_right ht
  refine conj_closure fun v hv => ?_
  obtain ⟨i, hi, rfl⟩ := mem_olT.mp hv
  have hwb : ∀ a ∈ wcj.getD i [], a < 2 * r := getD_bnd (fun w hw => bnd_iff.mp (hb w hw)) i
  have e := (eqP_iff hf (fun x hx => by
      simp only [sh, List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hA a (by have := hwb a ha; omega))
    (fun x hx => by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hA (2 * r) (by omega)
      · exact hA i (by omega)
      · exact hA (2 * r) (by omega))).mp (he i hi)
  rw [hti]
  have e2 : wp Γ n T [α + 2 * r, α + i, α + 2 * r] =
      el Γ n T (α + 2 * r) * el Γ n T (α + i) * el Γ n T (α + 2 * r) := by
    simp [wp, mul_assoc]
  rw [← e2, ← e, wp_sh]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (mem_olT.mpr ⟨a, hwb a ha, rfl⟩)

theorem fix_sound {bl : List (List ℕ)} {vs : List ℕ} (hnd : ∀ b ∈ bl, b.Nodup)
    (hlt : ∀ b ∈ bl, ∀ p ∈ b, p < n) (hv : ∀ v ∈ vs, ∃ g : Γ, Rep n T v g)
    (hc : fixChk T bl vs = true) : ∀ v ∈ vs, ∀ i, el Γ n T v • bPt n bl i = bPt n bl i := by
  simp only [fixChk, List.all_eq_true] at hc
  intro v hvs i
  have hmem : bl.getD i.1 [] ∈ bl := by
    rw [List.getD_eq_getElem _ _ i.2]
    exact List.getElem_mem _
  refine smul_blk_eq (hnd _ hmem) (hnd _ hmem) (hlt _ hmem) rfl fun p hp => ?_
  have h1 := hc v hvs _ hmem p hp
  rw [el_rep (hv v hvs) p (hlt _ hmem p hp)] at h1
  simpa using h1

@[expose] noncomputable def letE (S gw : List (List ℕ)) (sE ab : ℕ → Γ) (l : ℕ) : Γ :=
  if l < S.length then sE l else ((gw.getD (l - S.length) []).map ab).prod

theorem letters_sound {AB S gw : List (List ℕ)} {sE ab : ℕ → Γ}
    (hS : ∀ i < S.length, Rep n S i (sE i)) (hAB : ∀ i < AB.length, Rep n AB i (ab i))
    (hc : letChk T AB S gw n = true) :
    ∀ l < S.length + gw.length, Rep n T l (letE S gw sE ab l) := by
  obtain ⟨h1, h2⟩ := let_sound hS hAB hc
  intro l hl
  unfold letE
  split_ifs with h
  · exact h1 l h
  · obtain ⟨g, rfl⟩ : ∃ g, l = S.length + g := ⟨l - S.length, by omega⟩
    rw [Nat.add_sub_cancel_left]
    exact h2 g (by omega)

theorem el_mem_YT {nL l : ℕ} (hl : l < nL) : el Γ n T l ∈ YT Γ n T nL :=
  Subgroup.subset_closure ⟨l, hl, rfl⟩

theorem YT_le (nL : ℕ) :
    YT Γ n T nL ≤ Subgroup.closure {g | g ∈ (List.range nL).map (el Γ n T)} := by
  rw [YT, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact Subgroup.subset_closure (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)

theorem e2_sound (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {AB S gw : List (List ℕ)}
    {sE ab : ℕ → Γ} (hS : ∀ i < S.length, Rep n S i (sE i))
    (hAB : ∀ i < AB.length, Rep n AB i (ab i)) {xs : List (List ℕ × ℕ × ℕ)}
    {t : List ℕ × ℕ × ℕ} {ws vws : List (List ℕ)} {wit ex : List ℕ} {bl bi : List (List ℕ)}
    {r : ℕ} {spec : List (ℕ × List (List ℕ))} {tr : Bool} {cw : List ℕ} {alt : Bool}
    {wcj : List (List ℕ)} {b : List ℕ} (hr : 0 < r)
    (hc : e2Chk T AB S gw n xs t ws vws wit ex bl bi r spec tr cw alt wcj b = true) :
    (∀ l < S.length + gw.length, el Γ n T l = letE S gw sE ab l) ∧
    IdxTwoData (YT Γ n T (S.length + gw.length)) (olT Γ n T (S.length + gw.length) xs.length)
      (el Γ n T (S.length + gw.length + 2 * xs.length)) ∧
    (alt = true →
      (∀ v ∈ Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length},
        (el Γ n T (S.length + gw.length + 2 * xs.length))⁻¹ * v *
            el Γ n T (S.length + gw.length + 2 * xs.length) ∈
          Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length}) ∧
      el Γ n T (S.length + gw.length + 2 * xs.length) ∉
        Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length}) ∧
    (alt = false → el Γ n T (S.length + gw.length + 2 * xs.length) = 1) ∧
    ∃ (hpt : Function.Injective (bPt n bl))
      (hYp : ∀ z ∈ YT Γ n T (S.length + gw.length), ∀ i, ∃ j, z • bPt n bl i = bPt n bl j),
      (∀ v ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i)),
        v ∈ Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length}) ∧
      (∀ g ∈ olT Γ n T (S.length + gw.length) xs.length ++
          [el Γ n T (S.length + gw.length + 2 * xs.length)],
        ∀ v ∈ Subgroup.closure {v | v ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i))},
        g⁻¹ * v * g ∈ Subgroup.closure {v | v ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i))}) ∧
      (∀ a ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i)),
        ∀ c ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i)), a * c = c * a) ∧
      (∀ a ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i)), a * a = 1) ∧
      (∀ a ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i)),
        ∀ i, a • bPt n bl i = bPt n bl i) ∧
      Nat.card (Subgroup.closure {v | v ∈ (List.range vws.length).map
          (fun i => el Γ n T (S.length + gw.length + 2 * xs.length + 1 + i))}) =
        2 ^ vws.length ∧
      r ∣ Nat.card (Subgroup.closure {e | e ∈ (olT Γ n T (S.length + gw.length) xs.length).map
        (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T (S.length + gw.length)) (bPt n bl) hpt hYp)}) ∧
      (tr = true → ∀ i j : Fin bl.length, ∃ e ∈ Subgroup.closure {e | e ∈
        (olT Γ n T (S.length + gw.length) xs.length).map
          (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T (S.length + gw.length)) (bPt n bl) hpt hYp)},
        e i = j) := by
  unfold e2Chk at hc
  have hall := List.all_eq_true.mp hc
  have hp : ∀ k < 2 * xs.length + 5,
      e2Part T AB S gw n xs t ws vws wit ex bl bi r spec tr cw alt wcj b k = true :=
    fun k hk => hall k (List.mem_range.mpr hk)
  set nL := S.length + gw.length with hnL
  set R := xs.length with hR
  have h0 := hp 0 (by omega)
  simp only [e2Part, Nat.beq_refl, cond_true] at h0
  have h1 := hp 1 (by omega)
  simp only [e2Part, show Nat.beq 1 0 = false from rfl, Nat.beq_refl, cond_false,
    cond_true] at h1
  have h2 := hp 2 (by omega)
  simp only [e2Part, show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
    Nat.beq_refl, cond_false, cond_true, Bool.and_eq_true] at h2
  obtain ⟨⟨⟨⟨⟨hvb, hveq⟩, hci⟩, hwit⟩, hblk⟩, hfix⟩ := h2
  have h3 := hp 3 (by omega)
  simp only [e2Part, show Nat.beq 3 0 = false from rfl, show Nat.beq 3 1 = false from rfl,
    show Nat.beq 3 2 = false from rfl, Nat.beq_refl, cond_false, cond_true,
    Bool.and_eq_true] at h3
  obtain ⟨⟨himg, hcyc⟩, halt⟩ := h3
  have hnorm : ∀ a < 2 * R + 1,
      normA (tf T) (List.range n) (VW nL (2 * R + 1)) (VW (nL + 2 * R + 1) vws.length) ex a =
        true := by
    intro a ha
    have h := hp (a + 4) (by omega)
    simp only [e2Part, show Nat.beq (a + 4) 0 = false from rfl,
      show Nat.beq (a + 4) 1 = false from rfl, show Nat.beq (a + 4) 2 = false from rfl,
      show Nat.beq (a + 4) 3 = false from rfl, cond_false, Nat.add_sub_cancel] at h
    exact h
  have hlet := letters_sound hS hAB h0
  have hL : ∀ l < nL, ∃ g : Γ, Rep n T l g := fun l hl => ⟨_, hlet l hl⟩
  obtain ⟨hA, hid, -⟩ := alph_sound hf hL h1
  have hYol : ∀ a < 2 * R, el Γ n T (nL + a) ∈ YT Γ n T nL := fun a ha =>
    hid.mem _ (mem_olT.mpr ⟨a, ha, rfl⟩)
  have hgs : ∀ k < ((List.range (2 * R + 1)).map fun a => nL + a).length,
      ∃ g : Γ, Rep n T (((List.range (2 * R + 1)).map fun a => nL + a).getD k 0) g := by
    intro k hk
    rw [List.length_map, List.length_range] at hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simpa using hA k hk
  obtain ⟨hndb, hltb, hpt, hmap⟩ := blk_sound hgs hblk
  have hmap' : ∀ a < 2 * R + 1, ∀ i : Fin bl.length, ∃ hj : (bi.getD a []).getD i.1 0 < bl.length,
      el Γ n T (nL + a) • bPt n bl i = bPt n bl ⟨_, hj⟩ := by
    intro a ha i
    have := hmap a (by simpa using ha) i
    rwa [List.getD_eq_getElem ((List.range (2 * R + 1)).map fun a => nL + a) 0
      (by simpa using ha), List.getElem_map, List.getElem_range] at this
  have hYp : ∀ z ∈ YT Γ n T nL, ∀ i, ∃ j, z • bPt n bl i = bPt n bl j := by
    refine perm_of_gens hid.gen (bPt n bl) hpt fun g hg i => ?_
    rw [olT_append] at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hj, e⟩ := hmap' a (List.mem_range.mp ha) i
    exact ⟨_, e⟩
  have hb : ∀ a < 2 * R, ∀ i : Fin bl.length,
      (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T nL) (bPt n bl) hpt hYp (el Γ n T (nL + a)) i).val =
        tf bi a i.val := by
    intro a ha i
    obtain ⟨hj, e⟩ := hmap' a (by omega) i
    rw [rho_eq (hYol a ha) e]
    rfl
  have hfE : ∀ a < 2 * R, CFSG.Quasithin.A312M23.rhoFn (YT Γ n T nL) (bPt n bl) hpt hYp
      (el Γ n T (nL + a)) ∈ Subgroup.closure {e | e ∈ (olT Γ n T nL R).map
        (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T nL) (bPt n bl) hpt hYp)} := fun a ha =>
    Subgroup.subset_closure (List.mem_map.mpr ⟨_, mem_olT.mpr ⟨a, ha, rfl⟩, rfl⟩)
  have hveq' : ∀ i < vws.length, eqP T n [nL + 2 * R + 1 + i] (sh nL (vws.getD i [])) = true :=
    fun i hi => List.all_eq_true.mp hveq i (List.mem_range.mpr hi)
  obtain ⟨hvol, hVnorm, hvc, hvsq, hcard⟩ := vdata_sound hf hA hvb hveq' hci hwit hnorm
  have hvrep : ∀ v ∈ (List.range vws.length).map fun i => nL + 2 * R + 1 + i,
      ∃ g : Γ, Rep n T v g := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hi
    have hvb' := List.all_eq_true.mp hvb
    refine ⟨_, rep_of_eqP (fun x hx => ?_) (hveq' i (by omega))⟩
    simp only [sh, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hA a (by
      have := getD_bnd (fun w hw => bnd_iff.mp (hvb' w hw)) i a ha
      omega)
  have hvfix := fix_sound hndb hltb hvrep hfix
  refine ⟨fun l hl => el_eq hf (hlet l hl), hid, fun hat => ?_, fun haf => ?_, hpt, hYp, hvol,
    hVnorm, hvc, hvsq, fun a ha i => ?_, hcard, ?_, fun htr => ?_⟩
  · rw [hat] at halt
    simp only [cond_true, Bool.and_eq_true] at halt
    exact ⟨normW_sound hf hA hid.tsq halt.1, witB_sound hA halt.2⟩
  · rw [haf] at halt
    simp only [cond_false] at halt
    have := (idP_iff hf (u := [nL + 2 * R]) (fun l hl => by
      rw [List.mem_singleton.mp hl]
      exact hA (2 * R) (by omega))).mp halt
    rwa [wp_single] at this
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    exact hvfix _ (List.mem_map.mpr ⟨k, hk, rfl⟩) i
  · exact img_sound (f := fun a => el Γ n T (nL + a)) hr hYol hfE hb himg
  · rw [htr] at hcyc
    simp only [Bool.not_true, Bool.false_or] at hcyc
    have := cyc_sound (f := fun a => el Γ n T (nL + a)) hYol hfE hb hcyc
    exact this

theorem l34_sound (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) {AB S gw : List (List ℕ)}
    {sE ab : ℕ → Γ} (hS : ∀ i < S.length, Rep n S i (sE i))
    (hAB : ∀ i < AB.length, Rep n AB i (ab i)) {xs : List (List ℕ × ℕ × ℕ)}
    {t : List ℕ × ℕ × ℕ} {ws wcj : List (List ℕ)} {wu wv : List ℕ} {rels wxs : List (List ℕ)}
    (hc : l34Chk T AB S gw n xs t ws wcj wu wv rels wxs = true) :
    (∀ l < S.length + gw.length, el Γ n T l = letE S gw sE ab l) ∧
    IdxTwoData (YT Γ n T (S.length + gw.length)) (olT Γ n T (S.length + gw.length) xs.length)
      (el Γ n T (S.length + gw.length + 2 * xs.length)) ∧
    (∀ v ∈ Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length},
      (el Γ n T (S.length + gw.length + 2 * xs.length))⁻¹ * v *
          el Γ n T (S.length + gw.length + 2 * xs.length) ∈
        Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length}) ∧
    el Γ n T (S.length + gw.length + 2 * xs.length + 1) ∈
      Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length} ∧
    el Γ n T (S.length + gw.length + 2 * xs.length + 2) ∈
      Subgroup.closure {g | g ∈ olT Γ n T (S.length + gw.length) xs.length} ∧
    el Γ n T (S.length + gw.length + 2 * xs.length + 1) ≠ 1 ∧
    (∀ w ∈ rels, (w.map fun a => [el Γ n T (S.length + gw.length + 2 * xs.length + 1),
      el Γ n T (S.length + gw.length + 2 * xs.length + 2),
      (el Γ n T (S.length + gw.length + 2 * xs.length + 1))⁻¹,
      (el Γ n T (S.length + gw.length + 2 * xs.length + 2))⁻¹].getD a 1).prod = 1) ∧
    ∀ g ∈ olT Γ n T (S.length + gw.length) xs.length,
      g ∈ Subgroup.closure {el Γ n T (S.length + gw.length + 2 * xs.length + 1),
        el Γ n T (S.length + gw.length + 2 * xs.length + 2)} := by
  unfold l34Chk at hc
  have hall := List.all_eq_true.mp hc
  have hp : ∀ k < 4, l34Part T AB S gw n xs t ws wcj wu wv rels wxs k = true :=
    fun k hk => hall k (List.mem_range.mpr hk)
  set nL := S.length + gw.length with hnL
  set R := xs.length with hR
  have h0 := hp 0 (by omega)
  simp only [l34Part, Nat.beq_refl, cond_true] at h0
  have h1 := hp 1 (by omega)
  simp only [l34Part, show Nat.beq 1 0 = false from rfl, Nat.beq_refl, cond_false,
    cond_true] at h1
  have h2 := hp 2 (by omega)
  simp only [l34Part, show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
    Nat.beq_refl, cond_false, cond_true, Bool.and_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨hnw, hbu⟩, hbv⟩, heu⟩, hev⟩, hiu⟩, hiv⟩, hu1⟩ := h2
  have h3 := hp 3 (by omega)
  simp only [l34Part, show Nat.beq 3 0 = false from rfl, show Nat.beq 3 1 = false from rfl,
    show Nat.beq 3 2 = false from rfl, cond_false, Bool.and_eq_true, List.all_eq_true,
    List.mem_range] at h3
  obtain ⟨⟨⟨⟨hrb, hrel⟩, hwl⟩, hwb⟩, hwx⟩ := h3
  have hlet := letters_sound hS hAB h0
  have hL : ∀ l < nL, ∃ g : Γ, Rep n T l g := fun l hl => ⟨_, hlet l hl⟩
  obtain ⟨hA, hid, -⟩ := alph_sound hf hL h1
  set γ := nL + 2 * R + 1 with hγ
  have hsh : ∀ w : List ℕ, (∀ a ∈ w, a < 2 * R) → ∀ x ∈ sh nL w, ∃ g : Γ, Rep n T x g := by
    intro w hw x hx
    simp only [sh, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hA a (by have := hw a ha; omega)
  have hshm : ∀ w : List ℕ, (∀ a ∈ w, a < 2 * R) →
      wp Γ n T (sh nL w) ∈ Subgroup.closure {g | g ∈ olT Γ n T nL R} := by
    intro w hw
    rw [wp_sh]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (mem_olT.mpr ⟨a, hw a ha, rfl⟩)
  have hru := rep_of_eqP (hsh wu (bnd_iff.mp hbu)) heu
  have hrv := rep_of_eqP (hsh wv (bnd_iff.mp hbv)) hev
  have hrui := rep_inv hru hiu
  have hrvi := rep_inv hrv hiv
  have hue := el_eq hf hru
  have hve := el_eq hf hrv
  have huie := el_eq hf hrui
  have hvie := el_eq hf hrvi
  rw [← hue] at hrui huie
  rw [← hve] at hrvi hvie
  set u := el Γ n T (nL + 2 * R + 1) with hu
  set v := el Γ n T (nL + 2 * R + 2) with hv
  have h4 : ∀ a < 4, ∃ g : Γ, Rep n T (γ + a) g := by
    intro a ha
    interval_cases a
    · exact ⟨_, hru⟩
    · exact ⟨_, hrv⟩
    · exact ⟨_, hrui⟩
    · exact ⟨_, hrvi⟩
  have h4e : ∀ a < 4, el Γ n T (γ + a) = [u, v, u⁻¹, v⁻¹].getD a 1 := by
    intro a ha
    interval_cases a
    · rfl
    · rfl
    · exact huie
    · exact hvie
  have hsh4 : ∀ w : List ℕ, (∀ a ∈ w, a < 4) → ∀ x ∈ sh γ w, ∃ g : Γ, Rep n T x g := by
    intro w hw x hx
    simp only [sh, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact h4 a (hw a ha)
  have hwp4 : ∀ w : List ℕ, (∀ a ∈ w, a < 4) →
      wp Γ n T (sh γ w) = (w.map fun a => [u, v, u⁻¹, v⁻¹].getD a 1).prod := by
    intro w hw
    rw [wp_sh]
    congr 1
    exact List.map_congr_left fun a ha => h4e a (hw a ha)
  refine ⟨fun l hl => el_eq hf (hlet l hl), hid, normW_sound hf hA hid.tsq hnw,
    hue ▸ hshm wu (bnd_iff.mp hbu), hve ▸ hshm wv (bnd_iff.mp hbv), fun h => ?_,
    fun w hw => ?_, fun g hg => ?_⟩
  · have : idP T n [γ] = true :=
      (idP_iff hf (fun l hl => by rw [List.mem_singleton.mp hl]; exact ⟨_, hru⟩)).mpr
        (by rw [wp_single]; exact h)
    rw [this] at hu1
    exact absurd hu1 (by decide)
  · have hw4 : ∀ a ∈ w, a < 4 := bnd_iff.mp (hrb w hw)
    rw [← hwp4 w hw4]
    exact (idP_iff hf (hsh4 w hw4)).mp (hrel w hw)
  · obtain ⟨i, hi, rfl⟩ := mem_olT.mp hg
    have hwi : ∀ a ∈ wxs.getD i [], a < 4 := getD_bnd (fun w hw => bnd_iff.mp (hwb w hw)) i
    have e := (eqP_iff hf (hsh4 _ hwi) (u := sh γ (wxs.getD i [])) (v := [nL + i])
      (fun l hl => by rw [List.mem_singleton.mp hl]; exact hA i (by omega))).mp (hwx i hi)
    rw [wp_single, hwp4 _ hwi] at e
    rw [← e]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have ha4 := hwi a ha
    interval_cases a
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem lblk_sound {nL : ℕ} (hL : ∀ l < nL, ∃ g : Γ, Rep n T l g) {bl bi : List (List ℕ)}
    (hc : blkChk T n bl (List.range nL) bi = true) :
    (∀ b ∈ bl, b.Nodup) ∧ (∀ b ∈ bl, ∀ p ∈ b, p < n) ∧
    ∃ (hpt : Function.Injective (bPt n bl))
      (hYp : ∀ z ∈ YT Γ n T nL, ∀ i, ∃ j, z • bPt n bl i = bPt n bl j),
      ∀ l < nL, ∀ i : Fin bl.length,
        (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T nL) (bPt n bl) hpt hYp (el Γ n T l) i).val =
          tf bi l i.val := by
  have hgs : ∀ k < (List.range nL).length, ∃ g : Γ, Rep n T ((List.range nL).getD k 0) g := by
    intro k hk
    rw [List.length_range] at hk
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_range]
    exact hL k hk
  obtain ⟨hndb, hltb, hpt, hmap⟩ := blk_sound hgs hc
  have hmap' : ∀ l < nL, ∀ i : Fin bl.length, ∃ hj : (bi.getD l []).getD i.1 0 < bl.length,
      el Γ n T l • bPt n bl i = bPt n bl ⟨_, hj⟩ := by
    intro l hl i
    have := hmap l (by simpa using hl) i
    rwa [List.getD_eq_getElem (List.range nL) 0 (by simpa using hl), List.getElem_range] at this
  have hYp : ∀ z ∈ YT Γ n T nL, ∀ i, ∃ j, z • bPt n bl i = bPt n bl j := by
    refine perm_of_gens (YT_le nL) (bPt n bl) hpt fun g hg i => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hj, e⟩ := hmap' l (List.mem_range.mp hl) i
    exact ⟨_, e⟩
  refine ⟨hndb, hltb, hpt, hYp, fun l hl i => ?_⟩
  obtain ⟨hj, e⟩ := hmap' l hl i
  rw [rho_eq (el_mem_YT hl) e]
  rfl

theorem m22_sound {AB S gw : List (List ℕ)} {sE ab : ℕ → Γ}
    (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) (hS : ∀ i < S.length, Rep n S i (sE i))
    (hAB : ∀ i < AB.length, Rep n AB i (ab i)) {bl bi : List (List ℕ)} {wA wB gA gB : List ℕ}
    (hc : m22Chk T AB S gw n bl bi wA wB gA gB = true) :
    (∀ l < S.length + gw.length, el Γ n T l = letE S gw sE ab l) ∧ bl.length = 22 ∧
    ∃ (hpt : Function.Injective (bPt n bl))
      (hYp : ∀ z ∈ YT Γ n T (S.length + gw.length), ∀ i, ∃ j, z • bPt n bl i = bPt n bl j),
      wp Γ n T wA ∈ YT Γ n T (S.length + gw.length) ∧
      wp Γ n T wB ∈ YT Γ n T (S.length + gw.length) ∧
      (∀ i : Fin bl.length, (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T (S.length + gw.length))
        (bPt n bl) hpt hYp (wp Γ n T wA) i).val = gA.getD i.val 0) ∧
      ∀ i : Fin bl.length, (CFSG.Quasithin.A312M23.rhoFn (YT Γ n T (S.length + gw.length))
        (bPt n bl) hpt hYp (wp Γ n T wB) i).val = gB.getD i.val 0 := by
  simp only [m22Chk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨hlc, hl22⟩, hblk⟩, hbA⟩, hbB⟩, hgA⟩, hgB⟩ := hc
  have hlet := letters_sound hS hAB hlc
  have hL : ∀ l < S.length + gw.length, ∃ g : Γ, Rep n T l g := fun l hl => ⟨_, hlet l hl⟩
  obtain ⟨-, -, hpt, hYp, hrho⟩ := lblk_sound hL hblk
  have h22 := Nat.eq_of_beq_eq_true hl22
  have hY : ∀ w : List ℕ, (∀ a ∈ w, a < S.length + gw.length) →
      ∀ a ∈ w, el Γ n T a ∈ YT Γ n T (S.length + gw.length) :=
    fun w hw a ha => Subgroup.subset_closure ⟨a, hw a ha, rfl⟩
  refine ⟨fun l hl => el_eq hf (hlet l hl), h22, hpt, hYp,
    prod_mem_of (hY wA (bnd_iff.mp hbA)), prod_mem_of (hY wB (bnd_iff.mp hbB)),
    fun i => ?_, fun i => ?_⟩
  · rw [wp, rho_word wA (hY wA (bnd_iff.mp hbA)) (fun a ha => hrho a (bnd_iff.mp hbA a ha)) i]
    exact Nat.eq_of_beq_eq_true (hgA i.1 (h22 ▸ i.2))
  · rw [wp, rho_word wB (hY wB (bnd_iff.mp hbB)) (fun a ha => hrho a (bnd_iff.mp hbB a ha)) i]
    exact Nat.eq_of_beq_eq_true (hgB i.1 (h22 ▸ i.2))

theorem tri_sound {AB S gw : List (List ℕ)} {sE ab : ℕ → Γ}
    (hf : ∀ g : Γ, (∀ p < n, act n g p = p) → g = 1) (hS : ∀ i < S.length, Rep n S i (sE i))
    (hAB : ∀ i < AB.length, Rep n AB i (ab i)) {bl bi : List (List ℕ)}
    {x : List ℕ × ℕ × ℕ} (hc : triChk T AB S gw n bl bi x = true) :
    (∀ l < S.length + gw.length, el Γ n T l = letE S gw sE ab l) ∧ bl.length = 3 ∧
    ∃ (hpt : Function.Injective (bPt n bl))
      (_ : ∀ z ∈ YT Γ n T (S.length + gw.length), ∀ i, ∃ j, z • bPt n bl i = bPt n bl j),
      el Γ n T (S.length + gw.length) ∈ YT Γ n T (S.length + gw.length) ∧ x.2.2 % 2 = 1 ∧
      el Γ n T (S.length + gw.length) ^ x.2.2 = 1 ∧
      ∃ i, el Γ n T (S.length + gw.length) • bPt n bl i ≠ bPt n bl i := by
  simp only [triChk, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hlc, hl3⟩, hblk⟩, hbx⟩, hex⟩, hodd⟩, hord⟩, hmove⟩ := hc
  set nL := S.length + gw.length with hnL
  have hlet := letters_sound hS hAB hlc
  have hL : ∀ l < nL, ∃ g : Γ, Rep n T l g := fun l hl => ⟨_, hlet l hl⟩
  have hblk' := hblk
  simp only [blkChk, Bool.and_eq_true, Bool.not_eq_true'] at hblk'
  have hne := hblk'.1.1.1.1.1
  obtain ⟨-, hltb, hpt, hYp, -⟩ := lblk_sound hL hblk
  have h3 := Nat.eq_of_beq_eq_true hl3
  have hxw : ∀ l ∈ repW x.2.1 x.1, ∃ g : Γ, Rep n T l g := fun l hl =>
    hL l (bnd_iff.mp hbx l (mem_repW hl))
  have hrx := rep_of_eqP hxw hex
  have hxe := el_eq hf hrx
  have hxY : el Γ n T nL ∈ YT Γ n T nL := by
    rw [hxe]
    exact prod_mem_of fun a ha => Subgroup.subset_closure ⟨a, bnd_iff.mp hbx a (mem_repW ha), rfl⟩
  refine ⟨fun l hl => el_eq hf (hlet l hl), h3, hpt, hYp, hxY, Nat.eq_of_beq_eq_true hodd, ?_,
    ⟨0, by omega⟩, fun h => ?_⟩
  · have := (idP_iff hf (fun l hl => by
      have := mem_repW hl
      rw [List.mem_singleton.mp this]
      exact ⟨_, hrx⟩)).mp hord
    rwa [wp_repW, wp_single] at this
  · have hb0 : bl.getD 0 [] ∈ bl := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    obtain ⟨p, hp⟩ : ∃ p, (bl.getD 0 []).headD 0 = p ∧ p ∈ bl.getD 0 [] := by
      rcases hb : bl.getD 0 [] with _ | ⟨q, qs⟩
      · exfalso
        have e : bl.headD [] = bl.getD 0 [] := by
          rcases bl with _ | ⟨c, cs⟩
          · simp at h3
          · rfl
        rw [e, hb] at hne
        exact absurd hne (by decide)
      · exact ⟨q, rfl, List.mem_cons_self⟩
    obtain ⟨hpe, hpm⟩ := hp
    have hpn := hltb _ hb0 p hpm
    have hin : (⟨p, hpn⟩ : Fin n) ∈ bPt n bl ⟨0, by omega⟩ := hpm
    have hin2 : el Γ n T nL • (⟨p, hpn⟩ : Fin n) ∈ bPt n bl ⟨0, by omega⟩ := by
      rw [← h]
      exact Set.smul_mem_smul_set hin
    change (el Γ n T nL • (⟨p, hpn⟩ : Fin n)).val ∈ bl.getD 0 [] at hin2
    rw [← act_eq, ← el_rep ⟨_, hrx⟩ p hpn] at hin2
    rw [hpe] at hmove
    have h2 : (bl.getD 0 []).contains (tf T nL p) = true := List.elem_iff.mpr hin2
    rw [h2] at hmove
    exact absurd hmove (by decide)

end CFSG.KC.A312M23K

end

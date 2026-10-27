module

public import CFSG.Certificates.Kernel.SporLatDc2Act
public import CFSG.Certificates.Kernel.SporLatDcLists
public import Certificates.Data.Kernel.SporLatDc2

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.SLDc (sortedLt cntB anyB headL lexLt headL_min cntB_eq_length_filter lexLt_irrefl
  lexLt_trans)
open MulAction

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem mem_smul_iff (g : Γ) (x : PtL n) (q : Fin n) :
    (g • q).val ∈ (g • x).val ↔ q.val ∈ x.val := by
  rw [mem_smul_val]
  constructor
  · rintro ⟨p, hp, e⟩
    rw [← act_eq g q] at e
    rwa [act_inj (x.valid.2 p hp) q.isLt e] at hp
  · intro h
    exact ⟨q.val, h, act_eq g q⟩

theorem smul_mem_orbit' {α : Type*} [MulAction Γ α] {S : Subgroup Γ} {g : Γ} (hg : g ∈ S)
    {a b : α} (h : b ∈ orbit S a) : g • b ∈ orbit S a := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := h
  exact ⟨⟨g * k, S.mul_mem hg hk⟩, mul_smul g k a⟩

theorem length_filter_eq_ncard (f : ℕ → Bool) (x : PtL n) (hx : x.val.Nodup) :
    (x.val.filter f).length = {q : Fin n | f q.val = true ∧ q.val ∈ x.val}.ncard := by
  rw [← List.toFinset_card_of_nodup (hx.filter f), ← Set.ncard_coe_finset,
    ← Set.ncard_image_of_injective _ Fin.val_injective]
  congr 1
  ext p
  simp only [List.coe_toFinset, List.mem_filter, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hp, hf⟩
    exact ⟨⟨p, x.valid.2 p hp⟩, ⟨hf, hp⟩, rfl⟩
  · rintro ⟨q, ⟨hf, hq⟩, rfl⟩
    exact ⟨hq, hf⟩

variable [Finite Γ]

theorem image_meet {S : Subgroup Γ} {g : Γ} (hg : g ∈ S) (x : PtL n) (q : Fin n) :
    {y ∈ orbit S x | (g • q).val ∈ y.val} = (g • ·) '' {y ∈ orbit S x | q.val ∈ y.val} := by
  ext y
  constructor
  · rintro ⟨hy, hq⟩
    refine ⟨g⁻¹ • y, ⟨smul_mem_orbit' (S.inv_mem hg) hy, ?_⟩, smul_inv_smul g y⟩
    rw [← mem_smul_iff g, smul_smul, mul_inv_cancel, one_smul]
    exact hq
  · rintro ⟨z, ⟨hz, hq⟩, rfl⟩
    exact ⟨smul_mem_orbit' hg hz, (mem_smul_iff g z q).2 hq⟩

theorem image_pts {S : Subgroup Γ} {g : Γ} (hg : g ∈ S) (x : PtL n) (q₀ : Fin n) :
    {q ∈ orbit S q₀ | q.val ∈ (g • x).val} = (g • ·) '' {q ∈ orbit S q₀ | q.val ∈ x.val} := by
  ext q
  constructor
  · rintro ⟨hq, hx⟩
    refine ⟨g⁻¹ • q, ⟨smul_mem_orbit' (S.inv_mem hg) hq, ?_⟩, smul_inv_smul g q⟩
    rw [← mem_smul_iff g, smul_inv_smul]
    exact hx
  · rintro ⟨p, ⟨hp, hx⟩, rfl⟩
    exact ⟨smul_mem_orbit' hg hp, (mem_smul_iff g x p).2 hx⟩

theorem orbit_count (S : Subgroup Γ) (q₀ : Fin n) (x : PtL n) :
    (orbit S x).ncard * {q ∈ orbit S q₀ | q.val ∈ x.val}.ncard =
      (orbit S q₀).ncard * {y ∈ orbit S x | q₀.val ∈ y.val}.ncard := by
  classical
  have hAf : (orbit S x).Finite := Set.finite_range _
  have hOf : (orbit S q₀).Finite := Set.finite_range _
  rw [Set.ncard_eq_toFinset_card _ hAf, Set.ncard_eq_toFinset_card _ hOf]
  refine Finset.card_mul_eq_card_mul (fun (y : PtL n) (q : Fin n) => q.val ∈ y.val)
    (fun y hy => ?_) (fun q hq => ?_)
  · rw [Set.Finite.mem_toFinset] at hy
    obtain ⟨⟨g, hg⟩, rfl⟩ := hy
    show (hOf.toFinset.filter fun q => q.val ∈ (g • x).val).card = _
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp only [Set.Finite.mem_toFinset]
    show {q ∈ orbit S q₀ | q.val ∈ (g • x).val}.ncard = _
    rw [image_pts hg, Set.ncard_image_of_injective _ (MulAction.injective g)]
  · rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨⟨g, hg⟩, rfl⟩ := hq
    show (hAf.toFinset.filter fun y => (g • q₀).val ∈ y.val).card = _
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    simp only [Set.Finite.mem_toFinset]
    show {y ∈ orbit S x | (g • q₀).val ∈ y.val}.ncard = _
    rw [image_meet hg, Set.ncard_image_of_injective _ (MulAction.injective g)]

theorem headL_eq_of_mem_iff {l l' : List (List ℕ)} (h : sortedLt l = true)
    (h' : sortedLt l' = true) (hne : l ≠ []) (hmem : ∀ y, y ∈ l ↔ y ∈ l') : headL l = headL l' := by
  have hhead : ∀ {m : List (List ℕ)}, m ≠ [] → headL m ∈ m := fun {m} hm => by
    rcases m with _ | ⟨a, m⟩
    · exact absurd rfl hm
    · exact List.mem_cons_self
  have hne' : l' ≠ [] := by
    intro e
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil l hne
    rw [hmem, e] at hy
    exact List.not_mem_nil hy
  rcases headL_min h ((hmem _).2 (hhead hne')) with e | h1
  · exact e.symm
  · rcases headL_min h' ((hmem _).1 (hhead hne)) with e | h2
    · exact e
    · have e := lexLt_trans h1 h2
      rw [lexLt_irrefl] at e
      exact absurd e Bool.false_ne_true

theorem cntB_eq_zero_iff {α : Type} (f : α → Bool) (l : List α) :
    cntB f l = 0 ↔ ∀ a ∈ l, f a = false := by
  rw [cntB_eq_length_filter, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp

theorem anyB_beq_iff (q : ℕ) : ∀ l : List ℕ, anyB (Nat.beq q) l = true ↔ q ∈ l
  | [] => by simp [anyB]
  | a :: l => by rw [anyB, Bool.or_eq_true, Nat.beq_eq, anyB_beq_iff q l, List.mem_cons]

@[expose] def clSet (n : ℕ) (Cl : Clos) : Set (PtL n) := {y | y.val ∈ Cl.C.flatten}

theorem ncard_label_mem {T : Type*} (v : T → List ℕ) (hv : Function.Injective v)
    {L : List (List ℕ)} (hnd : L.Nodup) (hr : ∀ y ∈ L, ∃ z, v z = y) :
    {z | v z ∈ L}.ncard = L.length := by
  have himg : v '' {z | v z ∈ L} = (L.toFinset : Set (List ℕ)) := by
    ext y
    simp only [Set.mem_image, List.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      obtain ⟨z, rfl⟩ := hr y hy
      exact ⟨z, hy, rfl⟩
  rw [← Set.ncard_image_of_injective _ hv, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem ncard_clSet {n : ℕ} {Cl : Clos} (hnd : Cl.C.flatten.Nodup)
    (hv : ∀ y ∈ Cl.C.flatten, ∃ z : PtL n, z.val = y) :
    (clSet n Cl).ncard = Cl.C.flatten.length :=
  ncard_label_mem PtL.val (fun _ _ h => PtL.ext h) hnd hv

end CFSG.KC.SLD2

end

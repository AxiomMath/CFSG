module

public import CFSG.Sporadic.SuzOddCore.CTIFirst
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23L34Gen
public import Certificates.Certificate27140

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.LieType.Multipliers.L34
  CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Blueprint


@[expose] noncomputable def dWordPerm (w : List ℕ) : Equiv.Perm (Fin 42) := (w.map dperm).prod

theorem tabRep_dWord (w : List ℕ) (hw : ∀ j ∈ w, j < 5) :
    TabRep (wordTab 42 dGens w) (dWordPerm w) :=
  tabRep_wordTab (fun j hj => tabRep_dperm (by rw [dGens_size] at hj; exact hj)) w
    (fun j hj => by rw [dGens_size]; exact hw j hj)

theorem dWordPerm_mem (w : List ℕ) (hw : ∀ j ∈ w, j < 5) : dWordPerm w ∈ suzD := by
  refine suzD.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨j, hw j hj, rfl⟩

@[expose] def suzDLetPerm (u v : Equiv.Perm (Fin 42)) (l : Fin 2 × Bool) : Equiv.Perm (Fin 42) :=
  if l.2 then img2 u v l.1.val else (img2 u v l.1.val)⁻¹

theorem suzDLetPerm_mem (u v : Equiv.Perm (Fin 42)) (l : Fin 2 × Bool) :
    suzDLetPerm u v l ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 42))) := by
  obtain ⟨i, s⟩ := l
  have hu : u ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 42))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hv : v ∈ Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 42))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  fin_cases i <;> cases s <;> simp only [suzDLetPerm, img2] <;> simp <;>
    first | exact hu | exact hv

theorem tabRep_suzDWordTab {aT aI bT bI : Tab} {u v : Equiv.Perm (Fin 42)} (hu : TabRep aT u)
    (hui : TabRep aI u⁻¹) (hv : TabRep bT v) (hvi : TabRep bI v⁻¹) (w : List (Fin 2 × Bool)) :
    TabRep (suzDWordTab aT aI bT bI w) (w.map (suzDLetPerm u v)).prod := by
  have hlp : ∀ l, TabRep (suzDLetterTab aT aI bT bI l) (suzDLetPerm u v l) := by
    rintro ⟨i, s⟩
    fin_cases i <;> cases s <;> simp [suzDLetPerm, suzDLetterTab, img2, hu, hv, hui, hvi]
  induction w with
  | nil => exact TabRep.idTab
  | cons l w ih =>
    have e1 : suzDWordTab aT aI bT bI (l :: w) =
        comp 42 (suzDLetterTab aT aI bT bI l) (suzDWordTab aT aI bT bI w) := rfl
    rw [e1, List.map_cons, List.prod_cons]
    exact (hlp l).comp ih


theorem suzD_lieModel : LieModel ↥suzD .PSL 3 2 2 := by
  have h := Certificates.certificate27140
  simp only [suzDBridgeCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hsa, hsb⟩, hia⟩, hib⟩, hrels⟩, hgens⟩ := h
  have hwa : ∀ j ∈ suzDWordA, j < 5 := by decide
  have hwb : ∀ j ∈ suzDWordB, j < 5 := by decide
  obtain ⟨u, hu⟩ : ∃ u, u = dWordPerm suzDWordA := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = dWordPerm suzDWordB := ⟨_, rfl⟩
  obtain ⟨aT, haT⟩ : ∃ aT, aT = wordTab 42 dGens suzDWordA := ⟨_, rfl⟩
  obtain ⟨bT, hbT⟩ : ∃ bT, bT = wordTab 42 dGens suzDWordB := ⟨_, rfl⟩
  have hRu : TabRep aT u := by rw [haT, hu]; exact tabRep_dWord _ hwa
  have hRv : TabRep bT v := by rw [hbT, hv]; exact tabRep_dWord _ hwb
  rw [← haT] at hsa hia
  rw [← hbT] at hsb hib
  have hRui : TabRep (invTab 42 aT) u⁻¹ := hRu.inv hsa hia
  have hRvi : TabRep (invTab 42 bT) v⁻¹ := hRv.inv hsb hib
  have hword := tabRep_suzDWordTab hRu hRui hRv hRvi
  rw [← haT, ← hbT] at hrels hgens
  have hrel : ∀ w ∈ rels.map (List.map fun l => (l.1.val, l.2)), wordProd (img2 u v) w = 1 := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hw
    have h1 : wordProd (img2 u v) (r.map fun l => (l.1.val, l.2)) =
        (r.map (suzDLetPerm u v)).prod := by
      simp only [wordProd, List.map_map]
      rfl
    rw [h1]
    exact ((hword r).eq_iff TabRep.idTab).1 (hrels r hr)
  have hmemu : u ∈ suzD := hu ▸ dWordPerm_mem _ hwa
  have hmemv : v ∈ suzD := hv ▸ dWordPerm_mem _ hwb
  have hgen : suzD = Subgroup.closure {u, v} := by
    refine le_antisymm ?_ ((Subgroup.closure_le suzD).2 ?_)
    · rw [suzD, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj5 : j < 5 := hj
      have hrep := ((hword (suzDGenWords.getD j [])).eq_iff (tabRep_dperm hj5)).1 (hgens j hj5)
      rw [← hrep]
      exact Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact suzDLetPerm_mem u v l
    · rintro x (rfl | rfl)
      · exact hmemu
      · exact hmemv
  have hcard : 20160 ≤ Nat.card ↥suzD := card_suzD.ge
  exact Or.inl ⟨by decide, CFSG.Quasithin.A312M23.isPSL_three_four_of_gens hmemu hmemv hgen hrel
    hcard⟩

end CFSG.EvenSporadicStandard.Induction

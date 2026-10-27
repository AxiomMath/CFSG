module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cE
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cFus
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46TE

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8 L2K

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem w₁_pow_four : ∀ a : MC, a * MC.w₁ = MC.w₁ * a → a ^ 4 = 1 ∨ a ^ 4 = MC.w₁ := by
  decide +kernel

theorem ccount_w₁ : MC.ccount MC.w₁ = 64 := by decide +kernel

@[expose] def nineF2 : List MC :=
  [1, MC.z, MC.k, MC.z * MC.k, MC.t * MC.u, MC.z * (MC.t * MC.u), MC.k * (MC.t * MC.u),
    MC.z * MC.k * (MC.t * MC.u), MC.w₁]

theorem nineF2_nodup : nineF2.Nodup := by decide +kernel

theorem nineF2_mem : ∀ m ∈ nineF2, inE 7 m = true := by decide +kernel

theorem nineF2_span : ∀ m ∈ nineF2, m = MC.w₁ ∨ InSpan [MC.z, MC.z * MC.k, MC.t * MC.u] m := by
  decide +kernel

theorem Ereps_comm : ∀ i : Fin 8, ∀ a ∈ 0 :: Ereps i, ∀ b ∈ 0 :: Ereps i,
    crep a * crep b = crep b * crep a := by
  decide +kernel

theorem Ereps_sq : ∀ i : Fin 8, ∀ a ∈ 0 :: Ereps i, crep a * crep a = 1 := by decide +kernel

theorem Eh_elem {i : Fin 8} {x y : MC} (hx : inE i x = true) (hy : inE i y = true) :
    x * y = y * x ∧ x * x = 1 := by
  obtain ⟨hxR, hxc⟩ := cidx_of_inE hx
  obtain ⟨hyR, hyc⟩ := cidx_of_inE hy
  refine ⟨(crep_comm_iff hxR hyR).mp (Ereps_comm i _ (List.mem_cons.mpr hxc) _
    (List.mem_cons.mpr hyc)), ?_⟩
  rw [← crep_sq_of hxR]
  exact Ereps_sq i _ (List.mem_cons.mpr hxc)

theorem card_centralizer_MC (x : MC) :
    Nat.card (centralizer ({x} : Set MC)) = MC.ccount x := by
  classical
  rw [show Nat.card (centralizer ({x} : Set MC)) = Nat.card {g : MC // g * x = x * g} from
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_centralizer_singleton_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

@[expose] def nonT (t : X) (H : Subgroup X) : Set X := {x | x ∈ H ∧ ¬ ConjTo t x}

omit [Finite X] in
theorem conjTo_conj_iff (c f : X) : ConjTo t (c * f * c⁻¹) ↔ ConjTo t f := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨c⁻¹ * g, ?_⟩
    rw [show c⁻¹ * g * t * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * t * g⁻¹) * c by group, hg]
    group
  · rintro ⟨g, hg⟩
    refine ⟨c * g, ?_⟩
    rw [show c * g * t * (c * g)⁻¹ = c * (g * t * g⁻¹) * c⁻¹ by group, hg]

theorem ncard_nonT_E {yi ki ui : X} (D : S.Sec6 T₁ yi ki ui) (hE : Nat.card (S.E yi) = 16) :
    (nonT t (S.E yi)).ncard = 8 := by
  classical
  have : Fintype (S.E yi) := Fintype.ofFinite _
  have e1 : Nat.card {e : S.E yi // ConjTo t e} = Fintype.card {e : S.E yi // ConjTo t e} :=
    Nat.card_eq_fintype_card
  have e2 : Nat.card {e : S.E yi // ¬ ConjTo t e} =
      Fintype.card {e : S.E yi // ¬ ConjTo t e} := Nat.card_eq_fintype_card
  have e3 : Nat.card (S.E yi) = Fintype.card (S.E yi) := Nat.card_eq_fintype_card
  have h1 : Fintype.card {e : S.E yi // ConjTo t e} +
      Fintype.card {e : S.E yi // ¬ ConjTo t e} = 16 := by
    rw [Fintype.card_subtype_compl, Nat.add_sub_cancel' (Fintype.card_subtype_le _), ← e3, hE]
  rw [← e1, ← e2, D.card_conj] at h1
  have h2 : Nat.card {e : S.E yi // ¬ ConjTo t e} = (nonT t (S.E yi)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun e => ⟨e.1.1, e.1.2, e.2⟩
        invFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  omega

omit [Finite X] in
theorem nonT_map (c : X) (H : Subgroup X) :
    (fun x => c * x * c⁻¹) '' nonT t H = nonT t (H.map (MulAut.conj c).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyt⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, (conjTo_conj_iff c y).not.mpr hyt⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyt⟩
    exact ⟨y, ⟨hy, (conjTo_conj_iff c y).not.mp hyt⟩, rfl⟩

omit [Finite X] in
theorem ncard_nonT_map (c : X) (H : Subgroup X) :
    (nonT t (H.map (MulAut.conj c).toMonoidHom)).ncard = (nonT t H).ncard := by
  rw [← nonT_map, Set.ncard_image_of_injective _ (fun a b h => by simpa using h)]

namespace Conf

variable (K : Conf S T₁)

include K in
theorem not_conjTo_of_ncard_nonT {F : Subgroup X} (hF : ElemAbelianTwo F)
    (hcard : Nat.card F = 16) (h9 : 8 < (nonT t F).ncard) {h : X} (hh : h ∈ F) :
    ¬ ConjTo t h := by
  rintro ⟨g, rfl⟩
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hF'C : F' ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    have hac : a * (g * t * g⁻¹) = g * t * g⁻¹ * a := hF.comm a ha _ hh
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * a * g⁻¹⁻¹ * t = g⁻¹ * (a * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * a) * g := by rw [hac]
      _ = t * (g⁻¹ * a * g⁻¹⁻¹) := by group
  have hF'e := KD46.elem_map hF g⁻¹
  have hF'card : Nat.card F' = 16 := by
    rw [hF', card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hF'p : IsPGroup 2 F' := IsPGroup.of_card (n := 4) (by rw [hF'card]; norm_num)
  obtain ⟨c, -, hle⟩ := exists_conj_le_T (A := A) hF'p hF'C
  have hE := KD46.eq_E_of_card S hle (KD46.elem_map hF'e c)
    (by rw [card_map_of_injective (MulAut.conj c).injective, hF'card])
  have h8 : (nonT t (F'.map (MulAut.conj c).toMonoidHom)).ncard = 8 := by
    rcases hE with h | h <;> rw [h]
    · exact ncard_nonT_E K.D₁ (KD46.card_E₁ S)
    · exact ncard_nonT_E K.D₂ (KD46.card_E₂ S)
  rw [ncard_nonT_map, hF', ncard_nonT_map] at h8
  omega

theorem ι_w₁ : K.ι MC.w₁ = K.P.w₁N := K.P.ι_w₁

theorem not_conjTo_w₁ : ¬ ConjTo t (K.ι MC.w₁) := by
  have hp : IsPGroup 2 ((centralizer ({MC.w₁} : Set MC)).map K.ι) :=
    ((MC.isPGroup).to_subgroup _).map _
  refine not_conjTo_of_pow_four S hp ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : a * MC.w₁ = MC.w₁ * a := mem_centralizer_singleton_iff.mp ha
    refine mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ha', map_mul]
  · rw [card_map_of_injective K.ι_injective, card_centralizer_MC, ccount_w₁]
  · rintro _ ⟨a, ha, rfl⟩
    rcases w₁_pow_four a (mem_centralizer_singleton_iff.mp ha) with h | h
    · left; rw [← map_pow, h, map_one]
    · right; rw [← map_pow, h]

theorem elem_Ex (i : Fin 8) : ElemAbelianTwo (K.Ex i) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (Eh_elem ha hb).1]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, pow_two, (Eh_elem ha ha).2, map_one]

include K in
theorem not_conjTo_of_mem_E0₂ {e : X} (he : e ∈ S.E0 (S.x * S.y) (S.z * S.k)) :
    ¬ ConjTo t e :=
  VSide.not_conjTo_of_mem_E0 (side₂ S K.h4 K.D₁ K.D₂ K.hq₁ K.hq₂) he

theorem not_conjTo_of_mem_F₂ {h : X} (hh : h ∈ K.Ex 7) : ¬ ConjTo t h := by
  classical
  refine K.not_conjTo_of_ncard_nonT (K.elem_Ex 7) (K.card_Ex 7) ?_ hh
  have hsub : ((nineF2.map K.ι).toFinset : Set X) ⊆ nonT t (K.Ex 7) := by
    intro x hx
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨K.ι_mem_Ex (nineF2_mem m hm), ?_⟩
    rcases nineF2_span m hm with h | h
    · rw [h]; exact K.not_conjTo_w₁
    · refine K.not_conjTo_of_mem_E0₂ (map_mem_of_inSpan K.ι h fun g hg => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · rw [K.ι_z]; exact subset_closure (by simp)
      · rw [map_mul, K.ι_z, K.ι_k]; exact subset_closure (by simp)
      · rw [K.ι_tu]; exact subset_closure (by simp)
  have hcard : (nineF2.map K.ι).toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup (nineF2_nodup.map K.ι_injective), List.length_map]
    rfl
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, hcard] at this
  omega

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit

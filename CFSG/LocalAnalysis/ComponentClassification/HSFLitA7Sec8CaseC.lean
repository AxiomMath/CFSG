module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8CIota
public import CFSG.Quasithin.Background.A1cTransferVariants

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem xF_mul_xyF (F : S.Frame) : F.xF * (F.xF * F.yF) = S.z * F.yF := by
  rw [← mul_assoc, ← pow_two, F.xF_sq]

namespace MC

theorem card_centralizer (x : MC) : Nat.card (centralizer ({x} : Set MC)) = ccount x := by
  classical
  rw [show Nat.card (centralizer ({x} : Set MC)) = Nat.card {g : MC // g * x = x * g} from
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_centralizer_singleton_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end MC

namespace CPair

variable (P : CPair S F T₁)

theorem not_conjTo_of_ccount {x : MC} (hx : 32 < MC.ccount x) : ¬ ConjTo S.t (P.ι x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_conjTo_of_card (Q := (centralizer ({x} : Set MC)).map P.ι)
    ((MC.isPGroup.to_subgroup _).map P.ι) ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y * x = x * y := mem_centralizer_singleton_iff.mp hy
    rw [mem_centralizer_singleton_iff, ← map_mul, hy', map_mul]
  · rwa [card_map_of_injective P.ι_injective, MC.card_centralizer]

theorem w₁N_conj_x : P.w₁N * F.xF * P.w₁N⁻¹ = F.xF * P.V.ki := by
  rw [P.w₁N_eq, show P.V.D.w₁ * P.cN * F.xF * (P.V.D.w₁ * P.cN)⁻¹ =
    P.V.D.w₁ * (P.cN * F.xF * P.cN⁻¹) * P.V.D.w₁⁻¹ by group,
    S.central_of_mem_B P.cN_mem_B (xF_mem_T F), mul_inv_cancel_right, P.w₁_conj_x]

theorem w₁N_mem_T₁ : P.w₁N ∈ T₁ := by
  rw [P.w₁N_eq]
  exact mul_mem (w₁_mem_T₁ P.V.D) (P.h4.le (S.B_le_T P.cN_mem_B))

theorem card_S₁ : Nat.card P.V.D.S₁ = 256 := by
  rw [← P.range_ι, ← Nat.card_congr (MonoidHom.ofInjective P.ι_injective).toEquiv, MC.card_eq]
  norm_num

end CPair

structure CData (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  h4 : S.Sec4 F T₁
  D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF)
  D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)
  hq₁ : D₁.q0 = .extraspecial
  hq₂ : D₂.q0 = .extraspecial
  hu₁ : D₁.u = S.t * (F.xF * F.yF)
  hu₂ : D₂.u = S.t * (S.z * F.yF)

namespace CData

variable (C : CData S F T₁)

@[expose] noncomputable def V₁ : VSide S F T₁ where
  yi := F.yF
  ki := F.kF
  ui := F.xF * F.yF
  hyi := isRefl_yF F
  hki := isK_kF F
  hui := rfl
  D := C.D₁
  hq := C.hq₁
  hu := C.hu₁

@[expose] noncomputable def V₂ : VSide S F T₁ where
  yi := F.xF * F.yF
  ki := S.z * F.kF
  ui := S.z * F.yF
  hyi := isRefl_xyF F
  hki := isK_zkF F
  hui := (xF_mul_xyF F).symm
  D := C.D₂
  hq := C.hq₂
  hu := C.hu₂

@[expose] noncomputable def P₁ : CPair S F T₁ where
  V := C.V₁
  W := C.V₂
  hyy := Or.inl rfl
  hkk := rfl
  h4 := C.h4

@[expose] noncomputable def P₂ : CPair S F T₁ where
  V := C.V₂
  W := C.V₁
  hyy := Or.inr (by
    change F.yF = S.z * (F.xF * (F.xF * F.yF))
    rw [xF_mul_xyF, ← mul_assoc, z_mul_z, one_mul])
  hkk := by
    change F.kF = S.z * (S.z * F.kF)
    rw [← mul_assoc, z_mul_z, one_mul]
  h4 := C.h4

noncomputable def M' : Subgroup X := MC.M.map C.P₁.ι

theorem M'_le : C.M' ≤ C.D₁.S₁ := by
  rw [M', show C.D₁.S₁ = C.P₁.V.D.S₁ from rfl, ← C.P₁.range_ι]
  exact map_le_range _ _

theorem card_M' : Nat.card C.M' = 128 := by
  rw [M', card_map_of_injective C.P₁.ι_injective, MC.card_M]

theorem relIndex_M' : C.M'.relIndex C.D₁.S₁ = 2 := by
  have h1 := card_mul_index (C.M'.subgroupOf C.D₁.S₁)
  rw [show Nat.card (C.M'.subgroupOf C.D₁.S₁) = Nat.card C.M' from
    Nat.card_congr (subgroupOfEquivOfLe C.M'_le).toEquiv, C.card_M',
    show Nat.card C.D₁.S₁ = 256 from C.P₁.card_S₁] at h1
  rw [relIndex]
  omega

theorem not_conj_M' {m : X} (hm : m ∈ C.M') : ¬ ConjTo S.t m := by
  intro hc
  obtain ⟨x, hx, rfl⟩ := hm
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hc
    rw [map_one] at hc
    exact S.t_ne_one (by
      calc S.t = c⁻¹ * (c * S.t * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group)
  have hx2 : x * x = 1 := by
    apply C.P₁.ι_injective
    obtain ⟨c, hc⟩ := hc
    rw [map_mul, ← hc, map_one, show c * S.t * c⁻¹ * (c * S.t * c⁻¹) = c * (S.t * S.t) * c⁻¹ by
      group, t_mul_t, mul_one, mul_inv_cancel]
  rcases MC.M_fact x hx hx2 hx1 with h | h | h | h
  · exact C.P₁.V.not_conjTo_of_mem_Q0 (C.P₁.ι_mem_Q0 h) hc
  · exact C.P₁.not_conjTo_Fside C.D₁ C.D₂ (C.P₁.ι_mem_Fside h) hc
  · exact C.P₂.not_conjTo_Fside C.D₁ C.D₂ (C.P₁.ι_mem_Fother h) hc
  · exact C.P₁.not_conjTo_of_ccount h hc

noncomputable def E4 : Subgroup X := MC.E4.map C.P₁.ι

theorem card_E4 : Nat.card C.E4 = 16 := by
  rw [E4, card_map_of_injective C.P₁.ι_injective, MC.card_E4]

theorem ι_xh : C.P₁.ι MC.xh = F.xF := by
  rw [MC.xh, map_mul, map_mul, C.P₁.ι_t, C.P₁.ι_u, C.P₁.ι_y, C.P₁.V.u_eq]
  change S.t * (S.t * (F.xF * F.yF)) * F.yF = F.xF
  rw [← mul_assoc, t_mul_t, one_mul, mul_assoc, ← pow_two, F.yF_sq, mul_one]

theorem ι_xhy : C.P₁.ι (MC.xh * MC.y) = F.xF * F.yF := by
  rw [map_mul, C.ι_xh, C.P₁.ι_y]; rfl

theorem ι_zk : C.P₁.ι (MC.z * MC.k) = S.z * F.kF := by
  rw [map_mul, C.P₁.ι_z, C.P₁.ι_k]; rfl

theorem ι_u₂ : C.P₁.ι MC.u₂ = C.D₂.u := by
  rw [MC.u₂, map_mul, map_mul, map_mul, C.ι_xh, C.P₁.ι_t, C.P₁.ι_y,
    show C.D₂.u = C.V₂.D.u from rfl, C.V₂.u_eq]
  rfl

theorem condA {a : MC} (ha : C.P₁.ι a = C.V₂.vN) : MC.CondA a := by
  have hi := C.P₁.ι_injective
  refine ⟨hi ?_, hi ?_, hi ?_, hi ?_, hi ?_, hi ?_, hi ?_⟩ <;>
    simp only [map_mul, map_inv, map_one, ha, C.ι_xh, C.ι_u₂, C.P₁.ι_z, C.P₁.ι_y, C.P₁.ι_t,
      C.P₁.ι_k]
  · exact C.V₂.vN_conj_z
  · exact C.V₂.vN_conj_yi
  · exact C.V₂.vN_conj_ki
  · exact C.V₂.vN_conj_t
  · exact C.V₂.vN_conj_x
  · rw [← pow_two]; exact C.V₂.vN_sq
  · exact C.V₂.u_comm_vN

theorem condB {b : MC} (hb : C.P₁.ι b = C.P₂.w₁N) : MC.CondB b := by
  have hi := C.P₁.ι_injective
  refine ⟨hi ?_, hi ?_, hi ?_, hi ?_, hi ?_, hi ?_, hi ?_⟩ <;>
    simp only [map_mul, map_inv, map_one, hb, C.ι_xh, C.ι_u₂, C.P₁.ι_z, C.P₁.ι_y, C.P₁.ι_t,
      C.P₁.ι_k]
  · exact C.P₂.w₁N_conj_t
  · exact C.P₂.w₁N_conj_z
  · exact C.P₂.w₁N_conj_ki
  · exact C.P₂.w₁N_conj_yi
  · exact C.P₂.w₁N_conj_x
  · exact C.P₂.w₁N_sq
  · exact C.P₂.u_conj_w₁N

theorem map_thL {a b : MC} (ha : C.P₁.ι a = C.V₂.vN) (hb : C.P₁.ι b = C.P₂.w₁N) :
    (MC.thL a b).map C.P₁.ι = MC.L7.map C.P₂.ι := by
  simp only [MC.thL, MC.L7, List.map_cons, List.map_nil, C.ι_u₂, ha, hb, C.P₁.ι_z, C.ι_xhy,
    C.P₁.ι_t, C.ι_zk, C.P₂.ι_u, C.P₂.ι_w₁, C.P₂.ι_v, C.P₂.ι_z, C.P₂.ι_y, C.P₂.ι_t, C.P₂.ι_k]
  rfl

theorem conj_E4gen {a b : MC} (ha : C.P₁.ι a = C.V₂.vN) (hb : C.P₁.ι b = C.P₂.w₁N) {e : MC}
    {bs bs' : List Bool} (h1 : e = nfProd (MC.thL a b) bs)
    (h2 : MC.w₂ * nfProd MC.L7 bs * MC.w₂⁻¹ = nfProd MC.L7 bs')
    (h3 : MC.inE2 (MC.w₂ * nfProd (MC.thL a b) bs' * MC.w₂⁻¹) = true) :
    (C.P₁.w₂N * C.P₂.w₂N) * C.P₁.ι e * (C.P₁.w₂N * C.P₂.w₂N)⁻¹ ∈ F.E₂ := by
  have hL := C.map_thL ha hb
  have he : C.P₁.ι e = C.P₂.ι (nfProd MC.L7 bs) := by rw [h1, map_nfProd, hL, ← map_nfProd]
  have h4 : C.P₂.w₂N * C.P₁.ι e * C.P₂.w₂N⁻¹ = C.P₁.ι (nfProd (MC.thL a b) bs') := by
    rw [he, ← C.P₂.ι_w₂, ← map_inv, ← map_mul, ← map_mul, h2, map_nfProd, ← hL, ← map_nfProd]
  have h5 := C.P₁.ι_mem_EW h3
  rw [map_mul, map_mul, map_inv, C.P₁.ι_w₂] at h5
  rw [show (C.P₁.w₂N * C.P₂.w₂N) * C.P₁.ι e * (C.P₁.w₂N * C.P₂.w₂N)⁻¹ =
    C.P₁.w₂N * (C.P₂.w₂N * C.P₁.ι e * C.P₂.w₂N⁻¹) * C.P₁.w₂N⁻¹ by group, h4]
  exact h5

theorem exists_getD_A {a : MC} (h : a ∈ MC.Alist) : ∃ i : Fin 4, MC.Alist.getD i 1 = a := by
  simp only [MC.Alist, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem exists_getD_B {b : MC} (h : b ∈ MC.Blist) : ∃ j : Fin 4, MC.Blist.getD j 1 = b := by
  simp only [MC.Blist, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem exists_getD_E4 {e : MC} (h : e ∈ MC.E4gens) : ∃ l : Fin 4, MC.E4gens.getD l 1 = e := by
  simp only [MC.E4gens, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem subConj_E4 : SubConj C.E4 F.E₂ := by
  obtain ⟨a, ha⟩ := C.P₁.mem_range_of_mem_S₁ (C.D₁.T₁_le C.V₂.vN_mem_T₁)
  obtain ⟨b, hb⟩ := C.P₁.mem_range_of_mem_S₁ (C.D₁.T₁_le C.P₂.w₁N_mem_T₁)
  obtain ⟨i, hi⟩ := exists_getD_A (MC.A_cands a (C.condA ha))
  obtain ⟨j, hj⟩ := exists_getD_B (MC.B_cands b (C.condB hb))
  set g := C.P₁.w₂N * C.P₂.w₂N with hg
  have hgen : ∀ e ∈ MC.E4gens, ((MulAut.conj g).toMonoidHom.comp C.P₁.ι) e ∈ F.E₂ := by
    intro e he
    obtain ⟨l, hl⟩ := exists_getD_E4 he
    obtain ⟨h1, h2, h3⟩ := MC.cross_cert i j l
    rw [hi, hj, hl] at h1
    rw [hi, hj] at h3
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact C.conj_E4gen ha hb h1 h2 h3
  have hle : C.E4.map (MulAut.conj g).toMonoidHom ≤ F.E₂ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have := map_mem_of_inSpan ((MulAut.conj g).toMonoidHom.comp C.P₁.ι) (MC.E4_span x hx) hgen
    simpa using this
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_map_of_injective (MulAut.conj g).injective, C.card_E4,
    show F.E₂ = S.E (F.xF * F.yF) from rfl, (isRefl_xyF F).card_E]

theorem E₁_le_S₁ : S.E F.yF ≤ C.D₁.S₁ := C.V₁.E_le_S₁

theorem maximal (hnc : ¬ SubConj F.E₁ F.E₂) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hle : C.D₁.S₁ ≤ Q) : Q = C.D₁.S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨g, hgQ, hgN, hgS⟩ : ∃ g ∈ Q, g ∈ normalizer (C.D₁.S₁ : Set X) ∧ g ∉ C.D₁.S₁ := by
    set I := C.D₁.S₁.subgroupOf Q with hI
    have hIne : I ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm (fun x hx => ?_) hle
      have : (⟨x, hx⟩ : Q) ∈ I := by rw [htop]; trivial
      exact this
    have hnil : Group.IsNilpotent Q := hQ.isNilpotent
    have hlt : I < normalizer (I : Set Q) :=
      Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
    obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨x, x.2, ?_, fun h => hxI h⟩
    have hxsub : x ∈ (normalizer (C.D₁.S₁ : Set X)).subgroupOf Q := by
      rw [subgroupOf_normalizer_eq hle]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  set A := (S.E F.yF).map (MulAut.conj g).toMonoidHom with hA
  have hgN' := mem_normalizer_iff.mp hgN
  have hA_le : A ≤ C.D₁.S₁ := by
    rintro _ ⟨e, he, rfl⟩
    exact (hgN' e).mp (C.E₁_le_S₁ he)
  have hA_norm : ∀ s ∈ C.D₁.S₁, ∀ a ∈ A, s * a * s⁻¹ ∈ A := by
    rintro s hs _ ⟨e, he, rfl⟩
    have hs' : g⁻¹ * s * g ∈ C.D₁.S₁ := by
      have := (hgN' (g⁻¹ * s * g)).mpr (by rwa [show g * (g⁻¹ * s * g) * g⁻¹ = s by group])
      exact this
    have he' := conj_mem_of_mem_normalizer (C.D₁.S₁_le hs') he
    refine ⟨g⁻¹ * s * g * e * (g⁻¹ * s * g)⁻¹, he', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hAel : ElemAbelianTwo A := by
    have hE := (isRefl_yF F).elemAbelianTwo_E
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hE.comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.sq_eq_one x hx, map_one]
  have hAcard : Nat.card A = 16 := by
    rw [hA, card_map_of_injective (MulAut.conj g).injective, (isRefl_yF F).card_E]
  have hτA : g * S.t * g⁻¹ ∈ A := ⟨S.t, t_mem_E _, rfl⟩
  obtain ⟨x, hx⟩ := C.P₁.mem_range_of_mem_S₁ (hA_le hτA)
  have hconj : ConjTo S.t (C.P₁.ι x) := ⟨g, hx.symm⟩
  have hxA : C.P₁.ι x ∈ A := by rw [hx]; exact hτA
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx
    exact S.t_ne_one (by
      calc S.t = g⁻¹ * (g * S.t * g⁻¹) * g := by group
        _ = 1 := by rw [← hx]; group)
  have hx2 : x * x = 1 := by
    apply C.P₁.ι_injective
    rw [map_mul, hx, map_one, show g * S.t * g⁻¹ * (g * S.t * g⁻¹) = g * (S.t * S.t) * g⁻¹ by
      group, t_mul_t, mul_one, mul_inv_cancel]
  have hq : MC.inQ0 x = false := by
    by_contra h
    exact C.P₁.V.not_conjTo_of_mem_Q0 (C.P₁.ι_mem_Q0 (by simpa using h)) hconj
  have hf1 : MC.inF1 x = false := by
    by_contra h
    exact C.P₁.not_conjTo_Fside C.D₁ C.D₂ (C.P₁.ι_mem_Fside (by simpa using h)) hconj
  have hf2 : MC.inF2 x = false := by
    by_contra h
    exact C.P₂.not_conjTo_Fside C.D₁ C.D₂ (C.P₁.ι_mem_Fother (by simpa using h)) hconj
  have hcc : MC.ccount x ≤ 32 := not_lt.mp fun h => C.P₁.not_conjTo_of_ccount h hconj
  have hm : ∀ h : MC, C.P₁.ι (MC.cj h x) ∈ A := by
    intro h
    rw [MC.cj, map_mul, map_mul, map_inv]
    exact hA_norm _ (C.P₁.range_ι ▸ ⟨h, rfl⟩) _ hxA
  have hspan : ∀ {h₀ h₁ h₂ h₃ e : MC},
      InSpan [MC.cj h₀ x, MC.cj h₁ x, MC.cj h₂ x, MC.cj h₃ x] e → C.P₁.ι e ∈ A := by
    intro h₀ h₁ h₂ h₃ e he
    refine map_mem_of_inSpan C.P₁.ι he fun c hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact hm _
  rcases MC.syl_cert x (MC.syl_cands x hx2 hx1 hq hf1 hf2 hcc) with
    ⟨h₀, h₁, hnc'⟩ | ⟨h₀, h₁, h₂, h₃, hs⟩ | ⟨h₀, h₁, h₂, h₃, hs⟩
  ·
    apply hnc'
    apply C.P₁.ι_injective
    rw [map_mul, map_mul]
    exact hAel.comm _ (hm h₀) _ (hm h₁)
  ·
    have hz := hspan (hs MC.z (by simp))
    have hy := hspan (hs MC.y (by simp))
    have ht := hspan (hs MC.t (by simp))
    have hk := hspan (hs MC.k (by simp))
    rw [C.P₁.ι_z] at hz
    rw [C.P₁.ι_y] at hy
    rw [C.P₁.ι_t] at ht
    rw [C.P₁.ι_k] at hk
    have hE : S.E F.yF ≤ A := by
      rw [E_eq, C.V₁.B_eq]
      exact sup_le (sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hk)) (zpowers_le.mpr ht))
        (zpowers_le.mpr hy)
    have hAE : A = S.E F.yF :=
      (Subgroup.eq_of_le_of_card_ge hE (by rw [hAcard, (isRefl_yF F).card_E])).symm
    have hgE : g ∈ normalizer (S.E F.yF : Set X) := mem_normalizer_of_map_eq hAE
    have hmax := C.D₁.S₁_maximal (C.D₁.S₁ ⊔ zpowers g)
      (hQ.to_le (sup_le hle (zpowers_le.mpr hgQ))) le_sup_left
      (sup_le C.D₁.S₁_le (zpowers_le.mpr hgE))
    exact hgS (hmax ▸ mem_sup_right (mem_zpowers g))
  ·
    have hgen : ∀ e ∈ MC.E4gens, C.P₁.ι e ∈ A := fun e he => hspan (hs e he)
    have hE4 : C.E4 ≤ A := by
      rintro _ ⟨y, hy, rfl⟩
      exact map_mem_of_inSpan C.P₁.ι (MC.E4_span y hy) hgen
    have hAE : A = C.E4 :=
      (Subgroup.eq_of_le_of_card_ge hE4 (by rw [hAcard, C.card_E4])).symm
    obtain ⟨g', hg'⟩ := C.subConj_E4
    apply hnc
    refine ⟨g' * g, ?_⟩
    rw [← hg', ← hAE, hA, show F.E₁ = S.E F.yF from rfl, Subgroup.map_map]
    congr 1
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group

noncomputable def sylow (hnc : ¬ SubConj F.E₁ F.E₂) : Sylow 2 X where
  toSubgroup := C.D₁.S₁
  isPGroup' := C.D₁.isPGroup_S₁
  is_maximal' hQ hle := C.maximal hnc hQ hle

include C in
theorem false_of [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (hnc : ¬ SubConj F.E₁ F.E₂) : False := by
  obtain ⟨N, hN, hsq, htN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal (C.sylow hnc)
    (Q := C.M') C.M'_le C.relIndex_M' S.data.orderOf_t
    (fun x hx => C.not_conj_M' hx ⟨x⁻¹, by group⟩)
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · obtain ⟨a, b, hab⟩ := hX
    have hsq' : ∀ y : X, y * y = 1 := fun y => by
      have := hsq y
      rwa [h, mem_bot, pow_two] at this
    apply hab
    calc a * b = a * (a * b * (a * b)) * b := by rw [hsq', mul_one]
      _ = (a * a) * b * (a * (b * b)) := by group
      _ = b * a := by rw [hsq', hsq', one_mul, mul_one]
  · exact htN (h ▸ mem_top _)

end CData

end Sec8

end CFSG.ComponentClassification.HSFLit

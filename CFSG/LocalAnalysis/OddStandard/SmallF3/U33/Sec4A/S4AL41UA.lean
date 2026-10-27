module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41E8A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem u_comm {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  haveI : IsMulCommutative E := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) (⟨b, hb⟩ : E))

private theorem u_inv {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a : G}
    (ha : a ∈ E) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hE.2 a ha)

theorem l41_card_le_sq_inf_cent {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {v : G}
    (hnorm : ∀ e ∈ E, v * e * v⁻¹ ∈ E) (hv2 : v * v = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({v} : Set G)) *
      Nat.card ↥(E ⊓ centralizer ({v} : Set G)) := by
  have hvv : v * v = 1 := hv2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hvE : ∀ e ∈ E, v * e * v ∈ E := fun e he => by
    simpa [hvinv] using hnorm e he
  let φ : E →* E :=
    { toFun := fun e => ⟨(e : G) * (v * (e : G) * v), E.mul_mem e.2 (hvE (e : G) e.2)⟩
      map_one' := Subtype.ext (by
        change (1 : G) * (v * 1 * v) = 1
        rw [one_mul, mul_one, hvv])
      map_mul' := fun s t => Subtype.ext (by
        change (s : G) * t * (v * ((s : G) * t) * v) =
          (s : G) * (v * s * v) * (t * (v * t * v))
        have hc := u_comm hE t.2 (hvE s s.2)
        have h1 : v * ((s : G) * t) * v = (v * s * v) * (v * t * v) := by
          calc v * ((s : G) * t) * v = v * s * (v * v) * t * v := by rw [hvv]; group
            _ = (v * s * v) * (v * t * v) := by group
        rw [h1]
        calc (s : G) * t * ((v * s * v) * (v * t * v))
            = s * (t * (v * s * v)) * (v * t * v) := by group
          _ = s * ((v * s * v) * t) * (v * t * v) := by rw [hc]
          _ = s * (v * s * v) * (t * (v * t * v)) := by group) }
  set F := E ⊓ centralizer ({v} : Set G) with hF
  have hmemF : ∀ e : E, v * (e : G) * v = e → (e : G) ∈ F := fun e he => by
    refine Subgroup.mem_inf.mpr ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (e : G) * v = (v * e * v) * v := by rw [he]
      _ = v * e * (v * v) := by group
      _ = v * e := by rw [hvv, mul_one]
  have hker : φ.ker ≤ F.subgroupOf E := fun e he => by
    have h1 : (e : G) * (v * e * v) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    rw [eq_inv_of_mul_eq_one_right h1, u_inv hE e.2]
  have hrange : φ.range ≤ F.subgroupOf E := by
    rintro _ ⟨e, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    apply hmemF
    change v * ((e : G) * (v * e * v)) * v = (e : G) * (v * e * v)
    have hc := u_comm hE e.2 (hvE e e.2)
    calc v * ((e : G) * (v * e * v)) * v = v * ((v * e * v) * e) * v := by rw [hc]
      _ = (v * v) * e * v * e * v := by group
      _ = e * v * e * v := by rw [hvv, one_mul]
      _ = e * (v * e * v) := by group
  have hcardF : Nat.card (F.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcardF, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)

theorem l41_four_le_card_inf_cent_of_card_sixteen {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 16) {v : G}
    (hnorm : ∀ e ∈ E, v * e * v⁻¹ ∈ E) (hv2 : v * v = 1) :
    4 ≤ Nat.card ↥(E ⊓ centralizer ({v} : Set G)) := by
  have h := l41_card_le_sq_inf_cent hE hnorm hv2
  rw [hcard] at h
  by_contra hlt
  have h3 : Nat.card ↥(E ⊓ centralizer ({v} : Set G)) ≤ 3 := by omega
  have h9 := Nat.mul_le_mul h3 h3
  omega

theorem l41_no_e16_cent_conj (h : L41GPh1 t L S x₁ x₂ lam rho) {Q : Subgroup G}
    (hQe : CFSG.Open.IsElemAbelian 2 Q) (hQc : Nat.card Q = 16) (g : G)
    (hQ : Q ≤ centralizer ({g * t * g⁻¹} : Set G)) : False := by
  let Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'e : CFSG.Open.IsElemAbelian 2 Q' := hQe.map (MulAut.conj g⁻¹).toMonoidHom
  have hQ'c : Q' ≤ centralizer ({t} : Set G) := by
    rintro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqcomm : q * (g * t * g⁻¹) = (g * t * g⁻¹) * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQ hq)
    have hconj : (MulAut.conj g⁻¹) (g * t * g⁻¹) = t := by
      rw [MulAut.conj_apply]
      group
    have key : (MulAut.conj g⁻¹) q * t = t * (MulAut.conj g⁻¹) q := by
      have h := congrArg (MulAut.conj g⁻¹) hqcomm
      simpa only [map_mul, hconj] using h
    exact key
  obtain ⟨k, _hkH, hk⟩ := exists_conj_le_of_isPGroup hQ'c hQ'e.isPGroup h.toCtx0.le_invCent
    h.toCtx0.isPGroup h.toCtx0.relIndex_odd
  let Q'' : Subgroup G := Q'.map (MulAut.conj k).toMonoidHom
  have hQ''e : CFSG.Open.IsElemAbelian 2 Q'' := hQ'e.map (MulAut.conj k).toMonoidHom
  have hle : Q'' ≤ S := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hk q hq
  have hcard : Nat.card Q'' = 16 := by
    calc Nat.card Q'' = Nat.card Q' := Subgroup.card_map_of_injective (MulAut.conj k).injective
      _ = Nat.card Q := Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
      _ = 16 := hQc
  have h8 := h.basic.m2_S Q'' hle hQ''e
  omega

structure L41EData (t : G) (S 𝒮 E : Subgroup G) : Prop where
  S_le : S ≤ 𝒮
  cent : invCent t ⊓ 𝒮 = S
  normal_𝒮 : NormalIn E 𝒮
  elem : CFSG.Open.IsElemAbelian 2 E
  four_le : 4 ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set G))
  no_conj : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e

theorem L41EData.mem_conj {𝒮 E : Subgroup G} (d : L41EData t S 𝒮 E) {e k : G} (he : e ∈ E)
    (hk : k ∈ 𝒮) : k * e * k⁻¹ ∈ E :=
  d.normal_𝒮.2 k hk e he

theorem L41EData.cent_eq {𝒮 E : Subgroup G} (d : L41EData t S 𝒮 E) (hSt : S ≤ invCent t) :
    E ⊓ centralizer ({t} : Set G) = E ⊓ S := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hx' : x ∈ invCent t ⊓ 𝒮 := ⟨hx.2, d.normal_𝒮.1 hx.1⟩
    rwa [d.cent] at hx'
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    exact ⟨hx.1, hSt hx.2⟩


theorem L41EData.inf_S_eq (h : L41GPh2 t L S x₁ x₂ lam rho) {𝒮 E : Subgroup G}
    (d : L41EData t S 𝒮 E) : E ⊓ S = fourGrp x₁ x₂ := by
  have hE0 := d.cent_eq h.toCtx0.le_invCent
  have hES_A : E ⊓ S ≤ ctxE t x₁ x₂ := by
    have hN : NormalIn (E ⊓ S) S := by
      refine ⟨inf_le_right, ?_⟩
      intro g hg k hk
      rw [Subgroup.mem_inf] at hk ⊢
      exact ⟨d.mem_conj hk.1 (d.S_le hg), S.mul_mem (S.mul_mem hg hk.2) (S.inv_mem hg)⟩
    exact h.basic.normal_elem_le _ hN (CFSG.Open.IsElemAbelian.mono d.elem inf_le_left)
  have hES_F : E ⊓ S ≤ fourGrp x₁ x₂ := by
    intro a ha
    obtain ⟨f, hf, hfa | hfa⟩ := mem_ctxE_cases h.toCtx0 (hES_A ha)
    · rw [hfa]
      exact hf
    · exfalso
      obtain ⟨g, hg⟩ := (l41_tG_A h a (hES_A ha)).mpr ⟨f, hf, hfa⟩
      exact d.no_conj g a (Subgroup.mem_inf.mp ha).1 hg
  have hcardF : Nat.card (fourGrp x₁ x₂) = 4 := (h.wreath.fourGrp_eq_omega).2.2
  refine Subgroup.eq_of_le_of_card_ge hES_F ?_
  rw [hcardF, ← hE0]
  exact d.four_le

theorem L41EData.le_N (h : L41GPh2 t L S x₁ x₂ lam rho) {𝒮 E : Subgroup G}
    (d : L41EData t S 𝒮 E) : E ≤ l41N t x₁ x₂ := by
  have htS : t ∈ S := l41_e8_t_mem_S h.toL41GPh1
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hEF : E ⊓ S = fourGrp x₁ x₂ := d.inf_S_eq h
  have hE0 := d.cent_eq h.toCtx0.le_invCent
  have hFE : fourGrp x₁ x₂ ≤ E := hEF ▸ inf_le_left
  have hFA := l41_e8_fourGrp_le_ctxE t x₁ x₂
  have htA : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
  have hyF : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  intro e he
  have ht𝒮 : t ∈ 𝒮 := d.S_le htS
  obtain ⟨u, hu_def⟩ : ∃ u : G, u = t * e * t⁻¹ := ⟨_, rfl⟩
  have huE : u ∈ E := by
    rw [hu_def]
    exact d.mem_conj he ht𝒮
  have hte : t * e = u * t := by
    rw [hu_def]
    group
  have htu : t * u = e * t := by
    rw [hu_def]
    calc t * (t * e * t⁻¹) = (t * t) * e * t⁻¹ := by group
      _ = e * t := by rw [ht2, one_mul, htinv]
  have hcommu : u * e = e * u := l41_e8_comm d.elem huE he
  have hcent : e * u ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc t * (e * u) = (t * e) * u := by rw [mul_assoc]
      _ = (u * t) * u := by rw [hte]
      _ = u * (t * u) := by rw [mul_assoc]
      _ = u * (e * t) := by rw [htu]
      _ = (u * e) * t := by rw [mul_assoc]
      _ = (e * u) * t := by rw [hcommu]
  have hfu : e * u ∈ fourGrp x₁ x₂ := by
    have hmem : e * u ∈ E ⊓ centralizer ({t} : Set G) := ⟨E.mul_mem he huE, hcent⟩
    rw [hE0, hEF] at hmem
    exact hmem
  have hconj : e * t * e⁻¹ = (e * u) * t := by
    have hui : u⁻¹ = u := l41_e8_inv d.elem huE
    calc e * t * e⁻¹ = e * (t * e⁻¹ * t⁻¹) * t := by group
      _ = e * (t * e * t⁻¹)⁻¹ * t := by group
      _ = e * u⁻¹ * t := by rw [← hu_def]
      _ = (e * u) * t := by rw [hui]
  have hfix : ∀ f ∈ fourGrp x₁ x₂, e * f * e⁻¹ = f := fun f hf => by
    rw [l41_e8_comm d.elem he (hFE hf)]
    group
  have hconjA : ∀ a ∈ ctxE t x₁ x₂, e * a * e⁻¹ ∈ ctxE t x₁ x₂ := by
    intro a ha
    have ha' : a ∈ closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) := ha
    refine Subgroup.closure_induction
      (p := fun a _ => e * a * e⁻¹ ∈ ctxE t x₁ x₂) ?_ ?_ ?_ ?_ ha'
    · intro x hx
      show e * x * e⁻¹ ∈ ctxE t x₁ x₂
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · rw [hx, hconj]
        exact (ctxE t x₁ x₂).mul_mem (hFA hfu) htA
      · rw [hx, hfix _ hyF]
        exact hFA hyF
      · rw [hx, hfix _ hzF]
        exact hFA hzF
    · show e * 1 * e⁻¹ ∈ ctxE t x₁ x₂
      simp
    · intro x y _ _ hx hy
      show e * (x * y) * e⁻¹ ∈ ctxE t x₁ x₂
      have hxy : e * (x * y) * e⁻¹ = (e * x * e⁻¹) * (e * y * e⁻¹) := by group
      rw [hxy]
      exact (ctxE t x₁ x₂).mul_mem hx hy
    · intro x _ hx
      show e * x⁻¹ * e⁻¹ ∈ ctxE t x₁ x₂
      have hxi : e * x⁻¹ * e⁻¹ = (e * x * e⁻¹)⁻¹ := by group
      rw [hxi]
      exact (ctxE t x₁ x₂).inv_mem hx
  exact mem_normalizer_of_conj_mem hconjA

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

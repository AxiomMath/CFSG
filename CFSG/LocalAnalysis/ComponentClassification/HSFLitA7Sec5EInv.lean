module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5ER2

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec5E

open Sec7 Sec8 T2M

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

omit [Finite X] in
theorem map_conj_mul (H : Subgroup X) (a b : X) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext c
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_of_mem_normalizer {H : Subgroup X} {n : X} (hn : n ∈ normalizer (H : Set X)) :
    H.map (MulAut.conj n).toMonoidHom = H :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨a, ha, rfl⟩; exact conj_mem_of_mem_normalizer hn ha)
    (by rw [card_map_of_injective (MulAut.conj n).injective])

omit [Finite X] in
theorem map_conj_involution {H K : Subgroup X} {s : X} (hs : s * s = 1)
    (h : H.map (MulAut.conj s).toMonoidHom = K) : K.map (MulAut.conj s).toMonoidHom = H := by
  rw [← h, ← map_conj_mul, hs]
  ext a; simp

namespace Ctx

variable (C : Ctx S F T₁)

theorem ι_mem_N_E₅ (τ : T2M) : C.ι τ ∈ normalizer (C.E₅ : Set X) := by
  refine mem_normalizer_of_conj_le' fun a ha => ?_
  obtain ⟨a', rfl⟩ := C.exists_ι (C.E₅_le_T₂ ha)
  rw [← map_inv, ← map_mul, ← map_mul, C.ι_mem_E₅_iff]
  exact conj_E5 τ a' ((C.ι_mem_E₅_iff a').mp ha)

end Ctx

namespace R2D

variable {C : Ctx S F T₁} (B : R2D C)

@[expose] noncomputable def A' : Subgroup X := C.A.map (MulAut.conj B.g).toMonoidHom

@[expose] noncomputable def E₃' : Subgroup X := C.E₃.map (MulAut.conj B.g).toMonoidHom

theorem elemAbelianTwo_A' : ElemAbelianTwo B.A' := Ctx.elemAbelianTwo_map C.elemAbelianTwo_A _

theorem card_A' : Nat.card B.A' = 32 := by
  rw [A', card_map_of_injective (MulAut.conj _).injective, C.card_A]

theorem not_conjTo_of_mem_A' {a : X} (ha : a ∈ B.A') : ¬ ConjTo S.t a :=
  Ctx.not_conjTo_of_mem_elem B.elemAbelianTwo_A' B.card_A' ha

theorem E₃'_le_A' : B.E₃' ≤ B.A' := map_mono C.E₃_le_A

theorem w₂₂_mem_A' : B.w₂₂ ∈ B.A' := ⟨C.D.w₂, C.w₂_mem_A, rfl⟩

theorem ι_mem_E₃' {a : T2M} (ha : a ∈ B.G.p.E3'l) : C.ι a ∈ B.E₃' := by
  simp only [SigD.E3'l, List.mem_map] at ha
  obtain ⟨e, he, rfl⟩ := ha
  exact ⟨C.ι e, C.mem_E₃ he, by simp [MulAut.conj_apply, B.hσ]⟩

theorem A'_eq : B.A' = B.E₃' ⊔ zpowers B.w₂₂ := by
  rw [A', Ctx.A, Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

theorem elemAbelianTwo_E₃' : ElemAbelianTwo B.E₃' := Ctx.elemAbelianTwo_map C.elemAbelianTwo_E₃ _

theorem w₂₂_comm_E₃' : ∀ a ∈ B.E₃', B.w₂₂ * a = a * B.w₂₂ := by
  rintro _ ⟨a, ha, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, w₂₂]
  have h := C.w₂_comm_E₃ a ha
  calc B.g * C.D.w₂ * B.g⁻¹ * (B.g * a * B.g⁻¹) = B.g * (C.D.w₂ * a) * B.g⁻¹ := by group
    _ = B.g * (a * C.D.w₂) * B.g⁻¹ := by rw [h]
    _ = B.g * a * B.g⁻¹ * (B.g * C.D.w₂ * B.g⁻¹) := by group

theorem w₂₂_sq : B.w₂₂ ^ 2 = 1 := by
  rw [w₂₂, pow_two, show B.g * C.D.w₂ * B.g⁻¹ * (B.g * C.D.w₂ * B.g⁻¹) =
    B.g * (C.D.w₂ * C.D.w₂) * B.g⁻¹ by group, C.w₂_mul_w₂]; group

@[expose] noncomputable def fm : T2M := C.ιinv (B.q * B.q)

theorem ι_fm : C.ι B.fm = B.q * B.q := C.ι_ιinv B.f_mem_T₂

theorem hp' : B.G.p ∈ repList' := B.mem_repList'.1

theorem fm_mem_N : B.G.p.InN B.fm := B.mem_repList'.2

omit [Finite X] in
theorem conj_eq_of_inv {a b : X} (ha : a * a = 1) (hb : b * b = 1) :
    a * b * a⁻¹ = ((b * a) * (b * a))⁻¹ * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  simp only [mul_inv_rev, ha', hb', mul_assoc, hb, mul_one]

theorem f_sq : (B.q * B.q) * (B.q * B.q) = 1 := by
  rw [← B.ι_fm, ← map_mul, E3l_sq _ B.fm_mem_N.1, map_one]

theorem w₂₂_mul_w₂₂ : B.w₂₂ * B.w₂₂ = 1 := by rw [← pow_two, B.w₂₂_sq]

theorem w₂_conj_w₂₂ : C.D.w₂ * B.w₂₂ * C.D.w₂⁻¹ = (B.q * B.q) * B.w₂₂ := by
  rw [conj_eq_of_inv C.w₂_mul_w₂ B.w₂₂_mul_w₂₂, ← q, inv_eq_of_mul_eq_one_right B.f_sq]

theorem f_mem_E₃' : B.q * B.q ∈ B.E₃' := by rw [← B.ι_fm]; exact B.ι_mem_E₃' B.fm_mem_N.2

theorem aNorm : SigD.ANorm B.G.p := SigD.aNorm B.G.p B.hp'

theorem w₂_conj_A' {x : X} (hx : x ∈ B.A') : C.D.w₂ * x * C.D.w₂⁻¹ ∈ B.A' := by
  have hE : ∀ y ∈ B.E₃', C.D.w₂ * y * C.D.w₂⁻¹ ∈ B.A' := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [B.hσ, C.w₂_conj]
    refine B.E₃'_le_A' (B.ι_mem_E₃' (B.aNorm.2.1 _ ?_))
    simp only [SigD.E3'l, List.mem_map]
    exact ⟨e, he, rfl⟩
  rw [B.A'_eq] at hx
  rcases mem_or_of_mem_sup B.elemAbelianTwo_E₃' B.w₂₂_sq B.w₂₂_comm_E₃' hx with h | h
  · exact hE x h
  · have h1 := hE _ h
    have h2 : C.D.w₂ * B.w₂₂ * C.D.w₂⁻¹ ∈ B.A' := by
      rw [B.w₂_conj_w₂₂]; exact mul_mem (B.E₃'_le_A' B.f_mem_E₃') B.w₂₂_mem_A'
    have : C.D.w₂ * x * C.D.w₂⁻¹ =
        (C.D.w₂ * (x * B.w₂₂) * C.D.w₂⁻¹) * (C.D.w₂ * B.w₂₂ * C.D.w₂⁻¹)⁻¹ := by group
    rw [this]; exact mul_mem h1 (inv_mem h2)

@[expose] def ZlN (p : SigD) : Prop := ∀ c ∈ Zl, p.InN c

instance (p : SigD) : Decidable (ZlN p) := by unfold ZlN; infer_instance

theorem zlN : ∀ p ∈ repList', ZlN p := by decide +kernel

theorem card_Zl_filter : (Finset.univ.filter (· ∈ Zl)).card = 4 := by decide +kernel

theorem span_Zl : ∀ a ∈ Zl, InSpan [z, k] a := by decide +kernel

theorem ι_mem_zk_iff (a : T2M) :
    C.ι a ∈ (zpowers S.z ⊔ zpowers F.kF : Subgroup X) ↔ a ∈ Zl := by
  refine C.ι_mem_iff ((zk_le_B (isK_kF F)).trans (S.B_le_T.trans C.T_le_T₂))
    (fun b hb => C.ι_mem_of_span span_Zl (fun g hg => ?_) hb) ?_ a
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [C.ι_z]; exact mem_sup_left (mem_zpowers _)
    · rw [C.ι_k]; exact mem_sup_right (mem_zpowers _)
  · rw [card_zk (isK_kF F), card_Zl_filter]

theorem ι_mem_A_of_E3 {a : T2M} (ha : a ∈ E3l) : C.ι a ∈ C.A := C.E₃_le_A (C.mem_E₃ ha)

@[expose] noncomputable def NX : Subgroup X :=
  zpowers S.z ⊔ zpowers F.kF ⊔ zpowers (C.ι B.G.p.ws)

theorem ws_ok : SigD.WsOk B.G.p := SigD.wsOk B.G.p B.hp'

theorem NX_le : B.NX ≤ C.A ⊓ B.A' := by
  have hN : ∀ n : T2M, B.G.p.InN n → C.ι n ∈ C.A ⊓ B.A' := fun n hn =>
    ⟨ι_mem_A_of_E3 hn.1, B.E₃'_le_A' (B.ι_mem_E₃' hn.2)⟩
  have hZ := zlN B.G.p B.hp'
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le]
  · rw [← C.ι_z]; exact hN _ (hZ _ (by decide +kernel))
  · rw [← C.ι_k]; exact hN _ (hZ _ (by decide +kernel))
  · exact hN _ B.ws_ok.1

theorem card_NX : Nat.card B.NX = 8 := by
  have hV := elemAbelianTwo_zk (S := S) (isK_kF F)
  have hws2 : C.ι B.G.p.ws ^ 2 = 1 := by
    rw [pow_two, ← map_mul, E3l_sq _ B.ws_ok.1.1, map_one]
  have hnot : C.ι B.G.p.ws ∉ (zpowers S.z ⊔ zpowers F.kF : Subgroup X) := by
    rw [ι_mem_zk_iff]; exact B.ws_ok.2.1
  have hcomm : ∀ a ∈ (zpowers S.z ⊔ zpowers F.kF : Subgroup X),
      C.ι B.G.p.ws * a = a * C.ι B.G.p.ws :=
    fun a ha => C.elemAbelianTwo_A.comm _ (ι_mem_A_of_E3 B.ws_ok.1.1) _
      ((B.NX_le (mem_sup_left ha)).1)
  rw [NX, card_sup_of_not_mem hV hws2 hnot hcomm, card_zk (isK_kF F)]

theorem card_inf_ge : 8 ≤ Nat.card (C.A ⊓ B.A' : Subgroup X) := by
  rw [← B.card_NX]; exact Subgroup.card_le_of_le B.NX_le

theorem not_conjTo_of_mul {a a' : X} (ha : a ∈ C.A) (ha' : a' ∈ B.A')
    (hs : a * a' * (a * a') = 1) : ¬ ConjTo S.t (a * a') := by
  by_cases h1 : a' ∈ C.A
  · exact C.not_conjTo_of_mem_A (mul_mem ha h1)
  by_cases h2 : a ∈ B.A'
  · exact B.not_conjTo_of_mem_A' (mul_mem h2 ha')
  have ha2 : a * a = 1 := by rw [← pow_two]; exact C.elemAbelianTwo_A.sq_eq_one a ha
  have ha'2 : a' * a' = 1 := by rw [← pow_two]; exact B.elemAbelianTwo_A'.sq_eq_one a' ha'
  have hcomm : a * a' = a' * a := by
    have h3 : (a * a')⁻¹ = a * a' := inv_eq_of_mul_eq_one_right hs
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha'2, inv_eq_of_mul_eq_one_right ha2] at h3
    exact h3.symm
  set V₁ : Subgroup X := C.A ⊓ B.A' with hV₁
  have hV₁e : ElemAbelianTwo V₁ :=
    ⟨fun x hx y hy => C.elemAbelianTwo_A.comm x hx.1 y hy.1,
      fun x hx => C.elemAbelianTwo_A.sq_eq_one x hx.1⟩
  have hca : ∀ x ∈ V₁, a * x = x * a := fun x hx => C.elemAbelianTwo_A.comm a ha x hx.1
  have hV₂e : ElemAbelianTwo (V₁ ⊔ zpowers a) := elemAbelianTwo_sup hV₁e (by rwa [pow_two]) hca
  have hV₂A : V₁ ⊔ zpowers a ≤ C.A := sup_le inf_le_left (zpowers_le.mpr ha)
  have hca' : ∀ x ∈ V₁ ⊔ zpowers a, a' * x = x * a' := by
    intro x hx
    rcases mem_or_of_mem_sup hV₁e (by rwa [pow_two]) hca hx with h | h
    · exact B.elemAbelianTwo_A'.comm a' ha' x h.2
    · have h4 : x = (x * a) * a := by rw [mul_assoc, ha2, mul_one]
      rw [h4]
      have h5 := B.elemAbelianTwo_A'.comm a' ha' _ h.2
      calc a' * (x * a * a) = (a' * (x * a)) * a := by group
        _ = (x * a * a') * a := by rw [h5]
        _ = x * a * (a' * a) := by group
        _ = x * a * (a * a') := by rw [hcomm]
        _ = x * a * a * a' := by group
  have hV₃e : ElemAbelianTwo (V₁ ⊔ zpowers a ⊔ zpowers a') :=
    elemAbelianTwo_sup hV₂e (by rwa [pow_two]) hca'
  have hcard : 32 ≤ Nat.card (V₁ ⊔ zpowers a ⊔ zpowers a' : Subgroup X) := by
    rw [card_sup_of_not_mem hV₂e (by rwa [pow_two]) (fun h => h1 (hV₂A h)) hca',
      card_sup_of_not_mem hV₁e (by rwa [pow_two]) (fun h => h2 h.2) hca]
    have : 8 ≤ Nat.card V₁ := by rw [hV₁]; exact B.card_inf_ge
    omega
  have hmem : a * a' ∈ (V₁ ⊔ zpowers a ⊔ zpowers a' : Subgroup X) :=
    mul_mem (mem_sup_left (mem_sup_right (mem_zpowers a))) (mem_sup_right (mem_zpowers a'))
  exact not_conjTo_of_elem hV₃e
    (fun x hx => mem_centralizer_singleton_iff.mpr (hV₃e.comm x hx _ hmem)) hcard

theorem not_conjTo_one : ¬ ConjTo S.t (1 : X) := by
  rintro ⟨c, hc⟩
  apply S.t_ne_one
  have : S.t = c⁻¹ * (c * S.t * c⁻¹) * c := by group
  rw [this, hc]; group

include B in
theorem inv_cases_R {s : X} (h : s ∈ C.D.R) (hs2 : s * s = 1) :
    (∃ a ∈ B.G.p.S16, C.ι a = s) ∨ ¬ ConjTo S.t s := by
  rcases C.mem_R_cases h with hT | hT
  · obtain ⟨a, rfl⟩ := C.exists_ι hT
    have ha2 : a * a = 1 := C.ι_injective (by rw [map_mul, hs2, map_one])
    by_cases ha1 : a = 1
    · right; rw [ha1, map_one]; exact not_conjTo_one
    by_cases ha : a ∈ B.G.p.S16
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr fun hc => ha ((B.G.conjTo_iff ha2 ha1).mp hc)
  · right
    obtain ⟨τ, hτ⟩ := C.exists_ι hT
    have hs : s = C.ι τ * C.D.w₂ := by rw [hτ]; group
    have hτ2 : τ * sw2 τ = 1 := by
      apply C.ι_injective
      rw [map_mul, ← C.w₂_conj, map_one, ← hs2, hs, C.w₂_inv]
      group
    rw [hs]
    exact C.not_conjTo_of_mem_A (mul_mem (ι_mem_A_of_E3 (mem_E3_of_sw2 τ hτ2)) C.w₂_mem_A)

theorem g_sq_eq : ∃ c : T2M, C.ι c = B.g * B.g ∧ ¬ InT c := by
  obtain ⟨c, hc⟩ := C.exists_ι B.g_sq_mem
  exact ⟨c, hc, fun h => B.g_sq_not (hc ▸ (C.ι_mem_T_iff c).mpr h)⟩

theorem sq_ne_one_gT {τ : T2M} : (B.g * C.ι τ) * (B.g * C.ι τ) ≠ 1 := by
  obtain ⟨c, hc, hcT⟩ := B.g_sq_eq
  have h : (B.g * C.ι τ) * (B.g * C.ι τ) = C.ι (B.G.p.sig τ * c * τ) := by
    rw [map_mul, map_mul, ← B.hσ, hc]; group
  rw [h]
  intro h1
  have h2 : B.G.p.sig τ * c * τ = 1 := C.ι_injective (h1.trans (map_one C.ι).symm)
  have h3 : InT (B.G.p.sig τ * c * τ) := by rw [h2]; decide +kernel
  exact hcT ((SigD.z4 B.G.p B.G.hp τ c).mp h3)

theorem E₆_ne_E₁ : B.E₆ ≠ F.E₁ := by
  intro h
  obtain ⟨-, -, ⟨e, he, hne⟩, -⟩ := SigD.eDistinct B.G.p B.G.hp
  have h1 := (B.ι_mem_E₆_iff e).mpr he
  rw [h, C.ι_mem_E₁_iff] at h1
  exact hne h1

theorem w₂_mem_N_E₆ : C.D.w₂ ∈ normalizer (B.E₆ : Set X) := by
  refine mem_normalizer_of_conj_le' fun a ha => ?_
  have haT : a ∈ C.D.T₂ := by
    obtain ⟨b, hb, rfl⟩ := ha
    exact conj_mem_of_mem_normalizer B.g_mem_N (C.E₅_le_T₂ hb)
  obtain ⟨a', rfl⟩ := C.exists_ι haT
  rw [C.w₂_conj, B.ι_mem_E₆_iff]
  exact (SigD.eAct B.G.p B.G.hp).2.2.2.1 a' ((B.ι_mem_E₆_iff a').mp ha)

theorem sq_ne_one_gR {s : X} (h : B.g⁻¹ * s ∈ C.D.R) : s * s ≠ 1 := by
  rcases C.mem_R_cases h with hT | hT
  · obtain ⟨τ, hτ⟩ := C.exists_ι hT
    have hs : s = B.g * C.ι τ := by rw [hτ]; group
    rw [hs]; exact B.sq_ne_one_gT
  · intro hs2
    obtain ⟨τ, hτ⟩ := C.exists_ι hT
    have hs : s = B.g * (C.ι τ * C.D.w₂) := by rw [hτ]; group
    have hρ : B.g⁻¹ * s ∈ normalizer (F.E₁ : Set X) := C.D.R_le h
    have h1 : F.E₁.map (MulAut.conj s).toMonoidHom = F.E₂ := by
      rw [show s = B.g * (B.g⁻¹ * s) by group, map_conj_mul,
        map_conj_of_mem_normalizer hρ, B.conj_g_E₁]
    have h2 := map_conj_involution hs2 h1
    rw [hs, map_conj_mul, map_conj_mul, ← Ctx.E₅, map_conj_of_mem_normalizer (C.ι_mem_N_E₅ τ),
      ← E₆] at h2
    exact B.E₆_ne_E₁ h2

theorem sq_ne_one_w₂gR {s : X} (h : (C.D.w₂ * B.g)⁻¹ * s ∈ C.D.R) : s * s ≠ 1 := by
  rcases C.mem_R_cases h with hT | hT
  · intro hs2
    obtain ⟨τ, hτ⟩ := C.exists_ι hT
    have hs : s = C.D.w₂ * (B.g * C.ι τ) := by rw [hτ]; group
    have hρ : (C.D.w₂ * B.g)⁻¹ * s ∈ normalizer (F.E₁ : Set X) := C.D.R_le h
    have h1 : F.E₁.map (MulAut.conj s).toMonoidHom = C.E₅ := by
      rw [show s = C.D.w₂ * B.g * ((C.D.w₂ * B.g)⁻¹ * s) by group, map_conj_mul,
        map_conj_of_mem_normalizer hρ, B.conj_w₂g_E₁]
    have h2 := map_conj_involution hs2 h1
    rw [hs, map_conj_mul, map_conj_mul, map_conj_of_mem_normalizer (C.ι_mem_N_E₅ τ), ← E₆,
      map_conj_of_mem_normalizer B.w₂_mem_N_E₆] at h2
    exact B.E₆_ne_E₁ h2
  · obtain ⟨τ, hτ⟩ := C.exists_ι hT
    have hs : s = C.D.w₂ * (B.g * C.ι τ) * C.D.w₂⁻¹ := by
      rw [hτ, show C.D.w₂ * (B.g * ((C.D.w₂ * B.g)⁻¹ * s * C.D.w₂⁻¹)) * C.D.w₂⁻¹ =
        s * (C.D.w₂ * C.D.w₂)⁻¹ by group, C.w₂_mul_w₂, inv_one, mul_one]
    rw [hs]
    intro h1
    apply B.sq_ne_one_gT (τ := τ)
    have : (B.g * C.ι τ) * (B.g * C.ι τ) =
        C.D.w₂⁻¹ * ((C.D.w₂ * (B.g * C.ι τ) * C.D.w₂⁻¹) * (C.D.w₂ * (B.g * C.ι τ) * C.D.w₂⁻¹)) *
          C.D.w₂ := by group
    rw [this, h1]; group

theorem not_conjTo_gw₂gR {s : X} (h : (B.g * C.D.w₂ * B.g)⁻¹ * s ∈ C.D.R) (hs2 : s * s = 1) :
    ¬ ConjTo S.t s := by
  have hgg : ∀ τ : T2M, B.g * B.g * C.ι τ ∈ C.D.T₂ := fun τ =>
    mul_mem B.g_sq_mem (C.ι_mem_T₂ τ)
  rcases C.mem_R_cases h with hT | hT
  · obtain ⟨τ, hτ⟩ := C.exists_ι hT
    obtain ⟨τ₂, hτ₂⟩ := C.exists_ι (hgg τ)
    have hs : s = B.g * (C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂) * B.g⁻¹ := by
      rw [← C.w₂_conj, ← B.hσinv, hτ₂, hτ]; group
    have hs0 : (C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂) * (C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂) =
        1 := by
      have : (C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂) * (C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂) =
          B.g⁻¹ * (s * s) * B.g := by
        rw [hs]; group
      rw [this, hs2]; group
    have hτ2 : sw2 (B.G.p.sigInv τ₂) * sw2 (sw2 (B.G.p.sigInv τ₂)) = 1 := by
      apply C.ι_injective
      rw [map_mul, map_one, ← C.w₂_conj (sw2 (B.G.p.sigInv τ₂)), C.w₂_inv, ← hs0]
      group
    refine C.not_conjTo_of_conj_mem_A (n := B.g) ?_
    rw [hs, show B.g⁻¹ * (B.g * (C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂) * B.g⁻¹) * B.g =
      C.ι (sw2 (B.G.p.sigInv τ₂)) * C.D.w₂ by group]
    exact mul_mem (ι_mem_A_of_E3 (mem_E3_of_sw2 _ hτ2)) C.w₂_mem_A
  · obtain ⟨τ, hτ⟩ := C.exists_ι hT
    obtain ⟨τ₂, hτ₂⟩ := C.exists_ι (hgg τ)
    set τ₃ := B.G.p.sw22 τ₂ with hτ₃
    have hs : s = C.ι τ₃ * B.q := by
      rw [hτ₃, ← B.w₂₂_conj, hτ₂, q, w₂₂]
      calc s = B.g * C.D.w₂ * B.g * ((B.g * C.D.w₂ * B.g)⁻¹ * s * C.D.w₂⁻¹) * C.D.w₂ := by group
        _ = _ := by rw [hτ]; group
    have hsq : s * s = C.ι (τ₃ * B.G.p.sq τ₃ * B.fm) := by
      rw [map_mul, map_mul, ← B.q_conj, B.ι_fm, hs]; group
    have hτ₃1 : τ₃ * B.G.p.sq τ₃ * B.fm = 1 :=
      C.ι_injective (by rw [← hsq, hs2, map_one])
    have hM0 := SigD.qInv B.G.p B.hp' B.fm B.fm_mem_N τ₃ hτ₃1
    obtain ⟨e, he, e', he', hee⟩ := (SigD.m0Ok B.G.p B.hp').2 τ₃ hM0
    have hs' : s = (C.ι e * C.D.w₂) * (C.D.w₂ * (C.ι e' * B.w₂₂) * C.D.w₂⁻¹) := by
      rw [hs, hee, map_mul, q]
      calc C.ι e * C.ι e' * (B.w₂₂ * C.D.w₂) =
          C.ι e * (C.D.w₂ * C.D.w₂) * (C.ι e' * B.w₂₂) * C.D.w₂ := by
            rw [C.w₂_mul_w₂]; group
        _ = _ := by rw [C.w₂_inv]; group
    rw [hs'] at hs2 ⊢
    exact B.not_conjTo_of_mul (mul_mem (ι_mem_A_of_E3 he) C.w₂_mem_A)
      (B.w₂_conj_A' (mul_mem (B.E₃'_le_A' (B.ι_mem_E₃' he')) B.w₂₂_mem_A')) hs2

theorem inv_cases {s : X} (hs : s ∈ B.R₂) (hs2 : s * s = 1) :
    (∃ a ∈ B.G.p.S16, C.ι a = s) ∨ ¬ ConjTo S.t s := by
  rcases B.mem_cases hs with h | h | h | h
  · exact B.inv_cases_R h hs2
  · exact absurd hs2 (B.sq_ne_one_gR h)
  · exact absurd hs2 (B.sq_ne_one_w₂gR h)
  · exact Or.inr (B.not_conjTo_gw₂gR h hs2)

end R2D

end Sec5E

end CFSG.ComponentClassification.HSFLit

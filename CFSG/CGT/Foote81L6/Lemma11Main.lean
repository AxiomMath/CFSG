module

public import CFSG.CGT.Foote81L6.FinalCore
public import CFSG.CGT.Foote81L6.TStruct.Lemma2Three
public import CFSG.CGT.Foote81L6.Normalizer.Lemma10
public import CFSG.CGT.Foote81L6.Lemma6Key

public section

namespace CFSG.CGT.Foote81L6

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

namespace FooteCore

section Rep

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

theorem exists_conj_Frep01_of_fix_d₁ {F : Subgroup G} (hF : IsE64 T F) {d₁ y : G}
    (hd₁ : d₁ ∈ D.B₁) (hmove : ∃ v ∈ F, d₁ * v * d₁⁻¹ ≠ v) (hy : y ∈ F)
    (hfix : d₁ * y * d₁⁻¹ = y) : ∃ h ∈ T, y ∈ (D.Frep 0 1).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨α, hα, r₀, hr₀, r₁, hr₁, rfl⟩ := (D.mem_E64_iff hF).1 hy
  rw [D.conj_decomp_B₁ hd₁ (mem_inf.1 hα).2 (mem_inf.1 hr₀).2] at hfix
  have hr₁' := D.eq_one_or_b₁_of_fix_E64 hF hd₁ hmove hr₁ (mul_left_cancel (mul_left_cancel hfix))
  refine D.exists_conj_Frep01_of_mem rfl (mul_mem (mem_sup_left (mem_inf.1 hα).2)
    (mem_sup_right (mul_mem (mem_sup_left (mem_inf.1 hr₀).2) ?_))) (hF.mul_self _ hy)
  rcases hr₁' with rfl | rfl
  · exact mem_sup_right (one_mem _)
  · exact mem_sup_right (mem_zpowers _)

theorem exists_conj_Frep01_of_fix_d₀ {F : Subgroup G} (hF : IsE64 T F) {d₀ y : G}
    (hd₀ : d₀ ∈ D.B₀) (hmove : ∃ v ∈ F, d₀ * v * d₀⁻¹ ≠ v) (hy : y ∈ F)
    (hfix : d₀ * y * d₀⁻¹ = y) : ∃ h ∈ T, y ∈ (D.Frep 0 1).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨α, hα, r₀, hr₀, r₁, hr₁, rfl⟩ := (D.mem_E64_iff hF).1 hy
  have hαA := (mem_inf.1 hα).2
  have hr₁B := (mem_inf.1 hr₁).2
  rw [D.conj_decomp_B₀ hd₀ hαA hr₁B] at hfix
  have hfix' : d₀ * r₀ * d₀⁻¹ = r₀ := mul_right_cancel (mul_left_cancel hfix)
  have hr₀' := D.eq_one_or_b₀_of_fix_E64 hF hd₀ hmove hr₀ hfix'
  have hsA : D.s * α * D.s⁻¹ = α := by
    rw [(D.A_comm_B α hαA D.s D.s_mem_B).symm, mul_inv_cancel_right]
  set x := D.s * (α * (r₀ * r₁)) * D.s⁻¹ with hx_def
  have hxeq : x = α * ((D.s * r₁ * D.s⁻¹) * (D.s * r₀ * D.s⁻¹)) := by
    have hc : D.s * r₀ * D.s⁻¹ * (D.s * r₁ * D.s⁻¹) = D.s * r₁ * D.s⁻¹ * (D.s * r₀ * D.s⁻¹) :=
      D.B₀_comm_B₁ _ (D.conj_s_mem_B₀ hr₁B) _ (D.conj_s_mem_B₁ (mem_inf.1 hr₀).2) |>.symm
    calc x = (D.s * α * D.s⁻¹) * ((D.s * r₀ * D.s⁻¹) * (D.s * r₁ * D.s⁻¹)) := by
          rw [hx_def]; group
      _ = α * ((D.s * r₁ * D.s⁻¹) * (D.s * r₀ * D.s⁻¹)) := by rw [hsA, hc]
  have hxmem : x ∈ D.A ⊔ (D.B₀ ⊔ zpowers D.b₁) := by
    rw [hxeq]
    refine mul_mem (mem_sup_left hαA) (mem_sup_right (mul_mem (mem_sup_left
      (D.conj_s_mem_B₀ hr₁B)) (mem_sup_right ?_)))
    rcases hr₀' with h' | h'
    · rw [h', mul_one, mul_inv_cancel]; exact one_mem _
    · rw [h', D.conj_s_b₀]; exact mem_zpowers _
  have hx2 : x * x = 1 := by
    rw [hx_def]
    calc D.s * (α * (r₀ * r₁)) * D.s⁻¹ * (D.s * (α * (r₀ * r₁)) * D.s⁻¹)
        = D.s * ((α * (r₀ * r₁)) * (α * (r₀ * r₁))) * D.s⁻¹ := by group
      _ = 1 := by rw [hF.mul_self _ ((D.mem_E64_iff hF).2 ⟨α, hα, r₀, hr₀, r₁, hr₁, rfl⟩),
          mul_one, mul_inv_cancel]
  obtain ⟨h, hh, hxh⟩ := D.exists_conj_Frep01_of_mem rfl hxmem hx2
  refine ⟨D.s⁻¹ * h, mul_mem (inv_mem (D.B_le_T D.s_mem_B)) hh, ?_⟩
  obtain ⟨z, hz, hzx⟩ := hxh
  refine ⟨z, hz, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzx ⊢
  calc D.s⁻¹ * h * z * (D.s⁻¹ * h)⁻¹ = D.s⁻¹ * (h * z * h⁻¹) * D.s := by group
    _ = α * (r₀ * r₁) := by rw [hzx, hx_def]; group

end Rep

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

@[expose] def NBarDichotomy : Prop :=
  ∀ (F : Subgroup G) (hF : IsE64 (T : Subgroup G) F) [IsMulCommutative ↥F] (d₀ d₁ : G)
    (_ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (_ : d₀ ∉ F)
    (hd₀N : d₀ ∈ normalizer (F : Set G))
    (_ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (_ : d₁ ∉ F)
    (hd₁N : d₁ ∈ normalizer (F : Set G)),
    (HasNormalPComplement 2 (NBar.Q F) ∧ ∃ x₀ x₁ : NBar.Q F,
      pPrimeCore 2 (NBar.Q F) = zpowers x₀ ⊔ zpowers x₁ ∧
      x₀ * NBar.π F ⟨d₁, hd₁N⟩ = NBar.π F ⟨d₁, hd₁N⟩ * x₀ ∧
      x₁ * NBar.π F ⟨d₀, hd₀N⟩ = NBar.π F ⟨d₀, hd₀N⟩ * x₁ ∧
      (pPrimeCore 2 (NBar.Q F) ≠ ⊥ → ∀ (t' : G) (ht' : t' ∈ (T : Subgroup G) ⊓
          normalizer (F : Set G)), t' * t' = 1 → t' * D.t⁻¹ ∈ D.T₁ →
        Normalizer.Lemma11Hyp (NBar.ρ F) (NBar.π F ⟨d₀, hd₀N⟩) (NBar.π F ⟨d₁, hd₁N⟩) x₀ x₁
          (NBar.π F ⟨t', (mem_inf.1 ht').2⟩) ⟨D.b₀, D.b₀_mem_E64 hF⟩ ⟨D.b₁, D.b₁_mem_E64 hF⟩)) ∨
    ((∀ h ∈ (T : Subgroup G), F ≠ (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
      ∀ v : ↥F, (v : G) ∈ D.A ⊔ zpowers D.b → (∃ g : NBar.Q F, NBar.ρ F g v ≠ v) →
        ∃ x₀ : NBar.Q F, orderOf x₀ = 3 ∧
          NBar.π F ⟨d₁, hd₁N⟩ * x₀ = x₀ * NBar.π F ⟨d₁, hd₁N⟩ ∧ NBar.ρ F x₀ v ≠ v)

end FooteCore

theorem Normalizer.Lemma11Hyp.swap {V X : Type*} [CommGroup V] [Group X] {ρ : X →* MulAut V}
    {d₀ d₁ x₀ x₁ τ : X} {b₀ b₁ : V} (h : Normalizer.Lemma11Hyp ρ d₀ d₁ x₀ x₁ τ b₀ b₁)
    (hτ : τ * τ = 1) : Normalizer.Lemma11Hyp ρ d₁ d₀ x₁ x₀ τ b₁ b₀ where
  injective := h.injective
  sq_eq_one := h.sq_eq_one
  card_eq := h.card_eq
  tv₀ := h.tv₁
  tv₁ := h.tv₀
  ne_one₀ := h.ne_one₁
  ne_one₁ := h.ne_one₀
  ne := h.ne.symm
  orderOf₀ := h.orderOf₁
  orderOf₁ := h.orderOf₀
  comm := h.comm.symm
  core_eq := by rw [h.core_eq, sup_comm]
  inv₀ := h.inv₁
  inv₁ := h.inv₀
  comm₀₁ := h.comm₁₀
  comm₁₀ := h.comm₀₁
  conj := by
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
    calc τ * d₁ * τ⁻¹ = τ * (τ * d₀ * τ⁻¹) * τ⁻¹ := by rw [h.conj]
      _ = (τ * τ) * d₀ * (τ * τ)⁻¹ := by group
      _ = d₀ := by rw [hτ, one_mul, inv_one, mul_one]

namespace FooteData

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteData G (T : Subgroup G) 2 n)

theorem lemma11_of (hL3 : ∀ y ∈ D.Zab, IsConj D.a y → y = D.a)
    (hL4 : ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ ∉ D.T₁ →
      ∃ y : G, y * D.a * y⁻¹ ∈ D.T₁ ∧ y * D.a * y⁻¹ ∉ D.A ∧ y * D.a * y⁻¹ ∉ D.Astar)
    (hL5 : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ g : G,
      E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G), E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom)
    (hSylN : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G)))
    (hDich : D.toFooteCore.NBarDichotomy) :
    ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ = D.a := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxT, hxa⟩ := hcon
  have hTC : (T : Subgroup G) ≤ centralizer ({D.a} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.2 (D.a_comm_T hy)
  have hnorm : ∀ {x : G} {F : Subgroup G}, IsE64 (T : Subgroup G) F → x * D.a * x⁻¹ ∈ F →
      x * D.a * x⁻¹ ≠ D.a → ∃ x' ∈ normalizer (F : Set G), x' * D.a * x'⁻¹ ∈ F ∧
        x' * D.a * x'⁻¹ ≠ D.a := by
    intro x F hF hxF hxa
    obtain ⟨n', hn'N, h, hhT, -, hn'eq⟩ := exists_normalizer_conj (T.subtype hTC)
      (Sylow.coe_subtype T hTC) le_rfl (IsPGroup.of_card hF.2.2)
      (fun u hu v hv => TStruct.comm_of_mul_self hF.mul_self hu hv) hxF (hL5 F hF)
    have hha : h⁻¹ * D.a * h = D.a := by
      rw [mul_assoc, ← D.a_comm_T hhT, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hha] at hn'eq
    exact ⟨n', hn'N, by rw [hn'eq]; exact hxF, by rw [hn'eq]; exact hxa⟩
  have hstep : ∀ {x : G} {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F),
      x ∈ normalizer (F : Set G) → x * D.a * x⁻¹ ∈ F → x * D.a * x⁻¹ ≠ D.a →
      (∃ (x' : G) (F' : Subgroup G), IsE64 (T : Subgroup G) F' ∧
          (∃ h ∈ (T : Subgroup G), F' = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
          x' * D.a * x'⁻¹ ∈ F' ∧ x' * D.a * x'⁻¹ ≠ D.a) ∧
        ((∃ h ∈ (T : Subgroup G), F = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) → False) := by
    intro x F hF hxN hxF hxa
    haveI : IsMulCommutative ↥F :=
      ⟨⟨fun u v => Subtype.ext (TStruct.comm_of_mul_self hF.mul_self u.2 v.2)⟩⟩
    have haF : D.a ∈ F := D.a_mem_E64 hF
    have hval : ∀ (gN : ↥(normalizer (F : Set G))) (v : ↥F),
        ((NBar.ρ F (NBar.π F gN) v : ↥F) : G) = gN * v * (gN : G)⁻¹ := NBar.ρ_π F
    obtain ⟨d₀, hd₀R, -, hd₀F, hd₀N, -⟩ := D.exists_d₀ hF
    obtain ⟨d₁, hd₁R, -, hd₁F, hd₁N, -⟩ := D.exists_d₁ hF
    have hd₀B₀ : d₀ ∈ D.B₀ := (mem_inf.1 hd₀R).1
    have hd₁B₁ : d₁ ∈ D.B₁ := (mem_inf.1 hd₁R).1
    have hd₀T : d₀ ∈ (T : Subgroup G) := D.B_le_T (D.B₀_le_B hd₀B₀)
    have hd₁T : d₁ ∈ (T : Subgroup G) := D.B_le_T (D.B₁_le_B hd₁B₁)
    have hmove : ∀ {d : G}, d ∈ (T : Subgroup G) → d ∉ F → ∃ v ∈ F, d * v * d⁻¹ ≠ v := by
      intro d hdT hdF
      by_contra hcon
      push Not at hcon
      apply hdF
      have hmem : d ∈ (T : Subgroup G) ⊓ centralizer (F : Set G) := by
        refine mem_inf.2 ⟨hdT, mem_centralizer_iff.2 fun v hv => ?_⟩
        calc v * d = (d * v * d⁻¹) * d := by rw [hcon v hv]
          _ = d * v := by group
      rwa [D.centralizer_E64 hF] at hmem
    set w : ↥F := ⟨D.a, haF⟩ with hw_def
    have hxmove : NBar.ρ F (NBar.π F ⟨x, hxN⟩) w ≠ w := fun h' =>
      hxa (by have := congrArg Subtype.val h'; rwa [hval] at this)
    have hd₀w : NBar.ρ F (NBar.π F ⟨d₀, hd₀N⟩) w = w :=
      Subtype.ext (by rw [hval]; exact (by rw [D.a_comm_T hd₀T, mul_inv_cancel_right]))
    have hd₁w : NBar.ρ F (NBar.π F ⟨d₁, hd₁N⟩) w = w :=
      Subtype.ext (by rw [hval]; exact (by rw [D.a_comm_T hd₁T, mul_inv_cancel_right]))
    have hnew₁ : ∀ x₀ : NBar.Q F, NBar.π F ⟨d₁, hd₁N⟩ * x₀ = x₀ * NBar.π F ⟨d₁, hd₁N⟩ →
        NBar.ρ F x₀ w ≠ w → ∃ (x' : G) (F' : Subgroup G), IsE64 (T : Subgroup G) F' ∧
          (∃ h ∈ (T : Subgroup G), F' = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
          x' * D.a * x'⁻¹ ∈ F' ∧ x' * D.a * x'⁻¹ ≠ D.a := by
      intro x₀ hc hm
      obtain ⟨x₀N, rfl⟩ := NBar.π_surjective F x₀
      have hfix : NBar.ρ F (NBar.π F ⟨d₁, hd₁N⟩) (NBar.ρ F (NBar.π F x₀N) w) =
          NBar.ρ F (NBar.π F x₀N) w := by
        rw [← MulAut.mul_apply, ← map_mul, hc, map_mul, MulAut.mul_apply, hd₁w]
      have hfixG : d₁ * (NBar.ρ F (NBar.π F x₀N) w : G) * d₁⁻¹ = NBar.ρ F (NBar.π F x₀N) w := by
        have := congrArg Subtype.val hfix
        rwa [hval] at this
      obtain ⟨h, hh, hmem⟩ := D.exists_conj_Frep01_of_fix_d₁ hF hd₁B₁ (hmove hd₁T hd₁F)
        (NBar.ρ F (NBar.π F x₀N) w).2 hfixG
      refine ⟨x₀N, _, (D.isE64_Frep 0 1).map_conj hh, ⟨h, hh, rfl⟩, ?_, ?_⟩
      · rw [hval] at hmem; exact hmem
      · intro h'
        apply hm
        apply Subtype.ext
        rw [hval]
        exact h'
    have hnew₀ : ∀ x₁ : NBar.Q F, NBar.π F ⟨d₀, hd₀N⟩ * x₁ = x₁ * NBar.π F ⟨d₀, hd₀N⟩ →
        NBar.ρ F x₁ w ≠ w → ∃ (x' : G) (F' : Subgroup G), IsE64 (T : Subgroup G) F' ∧
          (∃ h ∈ (T : Subgroup G), F' = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
          x' * D.a * x'⁻¹ ∈ F' ∧ x' * D.a * x'⁻¹ ≠ D.a := by
      intro x₁ hc hm
      obtain ⟨x₁N, rfl⟩ := NBar.π_surjective F x₁
      have hfix : NBar.ρ F (NBar.π F ⟨d₀, hd₀N⟩) (NBar.ρ F (NBar.π F x₁N) w) =
          NBar.ρ F (NBar.π F x₁N) w := by
        rw [← MulAut.mul_apply, ← map_mul, hc, map_mul, MulAut.mul_apply, hd₀w]
      have hfixG : d₀ * (NBar.ρ F (NBar.π F x₁N) w : G) * d₀⁻¹ = NBar.ρ F (NBar.π F x₁N) w := by
        have := congrArg Subtype.val hfix
        rwa [hval] at this
      obtain ⟨h, hh, hmem⟩ := D.exists_conj_Frep01_of_fix_d₀ hF hd₀B₀ (hmove hd₀T hd₀F)
        (NBar.ρ F (NBar.π F x₁N) w).2 hfixG
      refine ⟨x₁N, _, (D.isE64_Frep 0 1).map_conj hh, ⟨h, hh, rfl⟩, ?_, ?_⟩
      · rw [hval] at hmem; exact hmem
      · intro h'
        apply hm
        apply Subtype.ext
        rw [hval]
        exact h'
    obtain ⟨Q, hQ⟩ := hSylN F hF
    rcases hDich F hF d₀ d₁ hd₀R hd₀F hd₀N hd₁R hd₁F hd₁N with
      ⟨hnc, x₀, x₁, hcore, hc₀, hc₁, hL11⟩ | ⟨hnF₂, hSig⟩
    ·
      have hDfix : ∀ y ∈ (NBar.sylowImage F Q : Subgroup (NBar.Q F)), NBar.ρ F y w = w := by
        intro y hy
        rw [NBar.coe_sylowImage] at hy
        obtain ⟨yN, hyQ, rfl⟩ := hy
        have hyT : (yN : G) ∈ (T : Subgroup G) := by
          have : yN ∈ (Q : Subgroup _) := hyQ
          rw [hQ, mem_subgroupOf] at this
          exact this
        apply Subtype.ext
        rw [hval]
        show (yN : G) * D.a * (yN : G)⁻¹ = D.a
        rw [D.a_comm_T hyT, mul_inv_cancel_right]
      set St : Subgroup (NBar.Q F) := (MulAction.stabilizer (MulAut ↥F) w).comap (NBar.ρ F)
        with hSt_def
      have hmemSt : ∀ g : NBar.Q F, g ∈ St ↔ NBar.ρ F g w = w := fun g => Iff.rfl
      have hOmove : ¬ pPrimeCore 2 (NBar.Q F) ≤ St := by
        intro hle
        apply hxmove
        obtain ⟨s', hs', o, ho, hso⟩ := Normalizer.exists_mul_of_hasNormalPComplement
          (NBar.sylowImage F Q) hnc (NBar.π F ⟨x, hxN⟩)
        rw [hso, map_mul, MulAut.mul_apply, (hmemSt o).1 (hle ho), hDfix s' hs']
      have hx01 : NBar.ρ F x₀ w ≠ w ∨ NBar.ρ F x₁ w ≠ w := by
        by_contra hcon
        push Not at hcon
        apply hOmove
        rw [hcore]
        exact sup_le (zpowers_le.2 ((hmemSt x₀).2 hcon.1)) (zpowers_le.2 ((hmemSt x₁).2 hcon.2))
      have hne : pPrimeCore 2 (NBar.Q F) ≠ ⊥ := fun h' => hOmove (h' ▸ bot_le)
      refine ⟨?_, fun hF₂ => ?_⟩
      · rcases hx01 with h₀ | h₁
        · exact hnew₁ x₀ hc₀.symm h₀
        · exact hnew₀ x₁ hc₁.symm h₁
      · obtain ⟨t', ht'N, ht'2, ht'T₁⟩ := D.exists_tprime rfl hF₂
        have h11 := hL11 hne t' ht'N ht'2 ht'T₁
        have ht'T := (mem_inf.1 ht'N).1
        have ht'N' := (mem_inf.1 ht'N).2
        rcases hx01 with h₀ | h₁
        · exact h₀ (D.lemma11_core hL3 hF hd₀B₀ hd₀N hd₁B₁ hd₁N ht'T ht'N' ht'2 ht'T₁ h11)
        ·
          have hτ : NBar.π F ⟨t', ht'N'⟩ * NBar.π F ⟨t', ht'N'⟩ = 1 := by
            rw [← map_mul]
            have : (⟨t', ht'N'⟩ : ↥(normalizer (F : Set G))) * ⟨t', ht'N'⟩ = 1 :=
              Subtype.ext ht'2
            rw [this, map_one]
          have h11s := h11.swap hτ
          have hL3s : ∀ y ∈ D.swap.Zab, IsConj D.swap.a y → y = D.swap.a := by
            have hZ : D.swap.Zab = D.Zab := by
              show closure {D.a, D.b₁, D.b₀} = closure {D.a, D.b₀, D.b₁}
              rw [Set.pair_comm D.b₁ D.b₀]
            rw [hZ]
            exact hL3
          have ht'T₁s : t' * D.swap.t⁻¹ ∈ D.swap.T₁ := by
            rw [FooteData.swap_toFooteCore, FooteCore.swap_T₁]
            exact ht'T₁
          exact h₁ (D.swap.lemma11_core hL3s hF hd₁B₁ hd₁N hd₀B₀ hd₀N ht'T ht'N' ht'2 ht'T₁s
            h11s)
    ·
      refine ⟨?_, fun ⟨h, hh, hFh⟩ => hnF₂ h hh hFh⟩
      obtain ⟨x₀, -, hx₀c, hx₀m⟩ := hSig w (mem_sup_left D.a_mem) ⟨_, hxmove⟩
      exact hnew₁ x₀ hx₀c hx₀m
  obtain ⟨x, hxT₁, hxa⟩ : ∃ x : G, x * D.a * x⁻¹ ∈ D.T₁ ∧ x * D.a * x⁻¹ ≠ D.a := by
    by_cases h : x * D.a * x⁻¹ ∈ D.T₁
    · exact ⟨x, h, hxa⟩
    · obtain ⟨y, hy, hyA, -⟩ := hL4 x hxT h
      exact ⟨y, hy, fun h' => hyA (by rw [h']; exact D.a_mem)⟩
  have hx2 : x * D.a * x⁻¹ * (x * D.a * x⁻¹) = 1 := by
    calc x * D.a * x⁻¹ * (x * D.a * x⁻¹) = x * (D.a * D.a) * x⁻¹ := by group
      _ = 1 := by rw [D.a_mul_a, mul_one, mul_inv_cancel]
  obtain ⟨F, hFT₁, hFab, hFcard, hxF⟩ := D.exists_elem64_of_mem_T₁ hxT₁ hx2
  have hF : IsE64 (T : Subgroup G) F := ⟨hFT₁.trans D.T₁_le_T, hFab, hFcard⟩
  obtain ⟨x', hx'N, hx'F, hx'a⟩ := hnorm hF hxF hxa
  obtain ⟨⟨x'', F', hF', hF'₂, hx''F, hx''a⟩, -⟩ := hstep hF hx'N hx'F hx'a
  obtain ⟨x₃, hx₃N, hx₃F, hx₃a⟩ := hnorm hF' hx''F hx''a
  exact (hstep hF' hx₃N hx₃F hx₃a).2 hF'₂

end FooteData

namespace FooteCore

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

private theorem fix_of_odd_of_sq_fix {X V : Type*} [Group X] [Group V] (ρ : X →* MulAut V)
    {x : X} (hx : Odd (orderOf x)) {v : V} (h2 : ρ (x * x) v = v) : ρ x v = v := by
  obtain ⟨k, hk⟩ := hx
  have hpow : ∀ m : ℕ, ρ ((x * x) ^ m) v = v := by
    intro m
    induction m with
    | zero => rw [pow_zero, map_one]; rfl
    | succ m ih => rw [pow_succ, map_mul, MulAut.mul_apply, h2, ih]
  have hxx : (x * x) ^ (k + 1) = x := by
    rw [← sq, ← pow_mul]
    calc x ^ (2 * (k + 1)) = x ^ (2 * k + 1) * x := by rw [← pow_succ]; ring_nf
      _ = x := by rw [← hk, pow_orderOf_eq_one, one_mul]
  rw [← hxx]
  exact hpow (k + 1)

theorem finalHalf_of (hcen : D.a ∈ center G)
    (hL42 : ∀ {a₁ : G}, a₁ ∈ D.A → a₁ ≠ 1 → a₁ ≠ D.a → ∀ g : G,
      g * a₁ * g⁻¹ ∈ (T : Subgroup G) → g * a₁ * g⁻¹ ∈ D.T₁)
    (hL5 : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∀ g : G,
      E.map (MulAut.conj g).toMonoidHom ≤ T →
      ∃ h ∈ (T : Subgroup G), E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom)
    (hSylN : ∀ E : Subgroup G, IsE64 (T : Subgroup G) E → ∃ Q : Sylow 2 ↥(normalizer (E : Set G)),
      (Q : Subgroup _) = (T : Subgroup G).subgroupOf (normalizer (E : Set G)))
    (hDich : D.NBarDichotomy) (hnA : ¬ StronglyInvolutionClosed D.A T) :
    ∃ h ∈ (T : Subgroup G), D.Astar = oddCent ((D.Frep 0 1).map (MulAut.conj h).toMonoidHom) := by
  classical
  have hcen' : ∀ y : G, y * D.a * y⁻¹ = D.a := fun y => by
    rw [mem_center_iff.1 hcen y, mul_inv_cancel_right]
  obtain ⟨a₁, ha₁, ha₁2, g, hgT, hgA⟩ : ∃ a₁ ∈ D.A, orderOf a₁ = 2 ∧ ∃ g : G,
      g * a₁ * g⁻¹ ∈ (T : Subgroup G) ∧ g * a₁ * g⁻¹ ∉ D.A := by
    by_contra hcon
    push Not at hcon
    exact hnA fun k hk hk2 g hg => hcon k hk hk2 g hg
  have ha₁1 : a₁ ≠ 1 := fun h' => by rw [h', orderOf_one] at ha₁2; exact absurd ha₁2 (by decide)
  have ha₁a : a₁ ≠ D.a := fun h' => hgA (by rw [h', hcen']; exact D.a_mem)
  obtain ⟨SK, hSK⟩ := D.sylow_centralizer_A hcen ha₁ ha₁1 ha₁a
  have hnorm : ∀ {x : G} {F : Subgroup G}, IsE64 (T : Subgroup G) F → x * a₁ * x⁻¹ ∈ F →
      x * a₁ * x⁻¹ ∉ D.A → ∃ x' ∈ normalizer (F : Set G), x' * a₁ * x'⁻¹ ∈ F ∧
        x' * a₁ * x'⁻¹ ∉ D.A := by
    intro x F hF hxF hxA
    obtain ⟨n', hn'N, h, hhT, hhF, hn'eq⟩ := exists_normalizer_conj SK hSK D.T₀_le_T
      (IsPGroup.of_card hF.2.2) (fun u hu v hv => TStruct.comm_of_mul_self hF.mul_self hu hv)
      hxF (hL5 F hF)
    have hhA : h⁻¹ * a₁ * h ∈ D.A := by
      have := (mem_normalizer_iff.1 (D.T_le_normalizer_A (inv_mem hhT)) a₁).1 ha₁
      rwa [inv_inv] at this
    rcases D.mem_A_of_two ha₁ ha₁1 ha₁a hhA with h' | h' | h' | h'
    · exfalso
      apply ha₁1
      calc a₁ = h * (h⁻¹ * a₁ * h) * h⁻¹ := by group
        _ = 1 := by rw [h']; group
    · exfalso
      apply ha₁a
      calc a₁ = h * (h⁻¹ * a₁ * h) * h⁻¹ := by group
        _ = D.a := by rw [h', hcen']
    · rw [h'] at hn'eq
      exact ⟨n', hn'N, by rw [hn'eq]; exact hxF, by rw [hn'eq]; exact hxA⟩
    · rw [h'] at hn'eq
      have haF : D.a ∈ F := D.a_mem_E64 hF
      have he : n' * a₁ * n'⁻¹ = D.a * (x * a₁ * x⁻¹) := by
        have h1 : n' * (D.a * a₁) * n'⁻¹ = D.a * (n' * a₁ * n'⁻¹) := by
          calc n' * (D.a * a₁) * n'⁻¹ = (n' * D.a * n'⁻¹) * (n' * a₁ * n'⁻¹) := by group
            _ = D.a * (n' * a₁ * n'⁻¹) := by rw [hcen']
        rw [h1] at hn'eq
        calc n' * a₁ * n'⁻¹ = D.a * (D.a * (n' * a₁ * n'⁻¹)) := by
              rw [← mul_assoc, D.a_mul_a, one_mul]
          _ = D.a * (x * a₁ * x⁻¹) := by rw [hn'eq]
      refine ⟨n', hn'N, by rw [he]; exact mul_mem haF hxF, fun hA => hxA ?_⟩
      rw [he] at hA
      have : x * a₁ * x⁻¹ = D.a * (D.a * (x * a₁ * x⁻¹)) := by
        rw [← mul_assoc, D.a_mul_a, one_mul]
      rw [this]
      exact mul_mem D.a_mem hA
  have hstep : ∀ {x : G} {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F),
      x ∈ normalizer (F : Set G) → x * a₁ * x⁻¹ ∈ F → x * a₁ * x⁻¹ ∉ D.A →
      (∃ (x' : G) (F' : Subgroup G), IsE64 (T : Subgroup G) F' ∧
          (∃ h ∈ (T : Subgroup G), F' = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
          x' * a₁ * x'⁻¹ ∈ F' ∧ x' * a₁ * x'⁻¹ ∉ D.A) ∧
        ((∃ h ∈ (T : Subgroup G), F = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) →
          D.Astar = oddCent F) := by
    intro x F hF hxN hxF hxA
    haveI : IsMulCommutative ↥F :=
      ⟨⟨fun u v => Subtype.ext (TStruct.comm_of_mul_self hF.mul_self u.2 v.2)⟩⟩
    have hAF : D.A ≤ F := D.A_le_E64 rfl hF
    have haF : D.a ∈ F := hAF D.a_mem
    have hval : ∀ (gN : ↥(normalizer (F : Set G))) (v : ↥F),
        ((NBar.ρ F (NBar.π F gN) v : ↥F) : G) = gN * v * (gN : G)⁻¹ := NBar.ρ_π F
    obtain ⟨d₀, hd₀R, -, hd₀F, hd₀N, -⟩ := D.exists_d₀ hF
    obtain ⟨d₁, hd₁R, -, hd₁F, hd₁N, -⟩ := D.exists_d₁ hF
    have hd₀B₀ : d₀ ∈ D.B₀ := (mem_inf.1 hd₀R).1
    have hd₁B₁ : d₁ ∈ D.B₁ := (mem_inf.1 hd₁R).1
    have hd₀T : d₀ ∈ (T : Subgroup G) := D.B_le_T (D.B₀_le_B hd₀B₀)
    have hd₁T : d₁ ∈ (T : Subgroup G) := D.B_le_T (D.B₁_le_B hd₁B₁)
    have hmove : ∀ {d : G}, d ∈ (T : Subgroup G) → d ∉ F → ∃ v ∈ F, d * v * d⁻¹ ≠ v := by
      intro d hdT hdF
      by_contra hcon
      push Not at hcon
      apply hdF
      have hmem : d ∈ (T : Subgroup G) ⊓ centralizer (F : Set G) := by
        refine mem_inf.2 ⟨hdT, mem_centralizer_iff.2 fun v hv => ?_⟩
        calc v * d = (d * v * d⁻¹) * d := by rw [hcon v hv]
          _ = d * v := by group
      rwa [D.centralizer_E64 hF] at hmem
    set w : ↥F := ⟨D.a, haF⟩ with hw_def
    set w₁ : ↥F := ⟨a₁, hAF ha₁⟩ with hw₁_def
    have hwfix : ∀ g : NBar.Q F, NBar.ρ F g w = w := by
      intro g
      obtain ⟨gN, rfl⟩ := NBar.π_surjective F g
      exact Subtype.ext (by rw [hval]; exact hcen' _)
    have hxmove : NBar.ρ F (NBar.π F ⟨x, hxN⟩) w₁ ≠ w₁ := fun h' => hxA (by
      have := congrArg Subtype.val h'
      rw [hval] at this
      rw [this]
      exact ha₁)
    have hd₀w₁ : NBar.ρ F (NBar.π F ⟨d₀, hd₀N⟩) w₁ = w₁ := Subtype.ext (by
      rw [hval]
      show d₀ * a₁ * d₀⁻¹ = a₁
      rw [← D.A_comm_B a₁ ha₁ d₀ (D.B₀_le_B hd₀B₀), mul_inv_cancel_right])
    have hd₁w₁ : NBar.ρ F (NBar.π F ⟨d₁, hd₁N⟩) w₁ = w₁ := Subtype.ext (by
      rw [hval]
      show d₁ * a₁ * d₁⁻¹ = a₁
      rw [← D.A_comm_B a₁ ha₁ d₁ (D.B₁_le_B hd₁B₁), mul_inv_cancel_right])
    have hout : ∀ y : NBar.Q F, Odd (orderOf y) → NBar.ρ F y w₁ ≠ w₁ →
        ((NBar.ρ F y w₁ : ↥F) : G) ∉ D.A := by
      intro y hy hm hA
      obtain ⟨yN, rfl⟩ := NBar.π_surjective F y
      have hv : ((NBar.ρ F (NBar.π F yN) w₁ : ↥F) : G) = yN * a₁ * (yN : G)⁻¹ := hval yN w₁
      rcases D.mem_A_of_two ha₁ ha₁1 ha₁a hA with h' | h' | h' | h'
      · rw [hv] at h'
        exact ha₁1 (conj_eq_one_iff.1 h')
      · rw [hv] at h'
        apply ha₁a
        calc a₁ = (yN : G)⁻¹ * (yN * a₁ * (yN : G)⁻¹) * yN := by group
          _ = D.a := by rw [h']; have := hcen' (yN : G)⁻¹; rwa [inv_inv] at this
      · exact hm (Subtype.ext h')
      ·
        have h1 : NBar.ρ F (NBar.π F yN) w₁ = w * w₁ := Subtype.ext h'
        apply hm
        apply fix_of_odd_of_sq_fix (NBar.ρ F) hy
        rw [map_mul, MulAut.mul_apply, h1, map_mul, hwfix, h1, ← mul_assoc]
        have hww : w * w = 1 := Subtype.ext D.a_mul_a
        rw [hww, one_mul]
    have hnew : ∀ y : NBar.Q F, Odd (orderOf y) → NBar.ρ F y w₁ ≠ w₁ →
        (NBar.π F ⟨d₁, hd₁N⟩ * y = y * NBar.π F ⟨d₁, hd₁N⟩ ∨
          NBar.π F ⟨d₀, hd₀N⟩ * y = y * NBar.π F ⟨d₀, hd₀N⟩) →
        ∃ (x' : G) (F' : Subgroup G), IsE64 (T : Subgroup G) F' ∧
          (∃ h ∈ (T : Subgroup G), F' = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) ∧
          x' * a₁ * x'⁻¹ ∈ F' ∧ x' * a₁ * x'⁻¹ ∉ D.A := by
      intro y hy hm hc
      have hyA := hout y hy hm
      obtain ⟨yN, rfl⟩ := NBar.π_surjective F y
      have hv : ((NBar.ρ F (NBar.π F yN) w₁ : ↥F) : G) = yN * a₁ * (yN : G)⁻¹ := hval yN w₁
      obtain ⟨h, hh, hmem⟩ : ∃ h ∈ (T : Subgroup G),
          ((NBar.ρ F (NBar.π F yN) w₁ : ↥F) : G) ∈
            (D.Frep 0 1).map (MulAut.conj h).toMonoidHom := by
        rcases hc with hc | hc
        · have hfix : NBar.ρ F (NBar.π F ⟨d₁, hd₁N⟩) (NBar.ρ F (NBar.π F yN) w₁) =
              NBar.ρ F (NBar.π F yN) w₁ := by
            rw [← MulAut.mul_apply, ← map_mul, hc, map_mul, MulAut.mul_apply, hd₁w₁]
          have hfixG := congrArg Subtype.val hfix
          rw [hval ⟨d₁, hd₁N⟩] at hfixG
          exact D.exists_conj_Frep01_of_fix_d₁ hF hd₁B₁ (hmove hd₁T hd₁F)
            (NBar.ρ F (NBar.π F yN) w₁).2 hfixG
        · have hfix : NBar.ρ F (NBar.π F ⟨d₀, hd₀N⟩) (NBar.ρ F (NBar.π F yN) w₁) =
              NBar.ρ F (NBar.π F yN) w₁ := by
            rw [← MulAut.mul_apply, ← map_mul, hc, map_mul, MulAut.mul_apply, hd₀w₁]
          have hfixG := congrArg Subtype.val hfix
          rw [hval ⟨d₀, hd₀N⟩] at hfixG
          exact D.exists_conj_Frep01_of_fix_d₀ hF hd₀B₀ (hmove hd₀T hd₀F)
            (NBar.ρ F (NBar.π F yN) w₁).2 hfixG
      rw [hv] at hmem hyA
      exact ⟨yN, _, (D.isE64_Frep 0 1).map_conj hh, ⟨h, hh, rfl⟩, hmem, hyA⟩
    obtain ⟨Q, hQ⟩ := hSylN F hF
    rcases hDich F hF d₀ d₁ hd₀R hd₀F hd₀N hd₁R hd₁F hd₁N with
      ⟨hnc, x₀, x₁, hcore, hc₀, hc₁, hL11⟩ | ⟨hnF₂, hSig⟩
    ·
      have hDA : ∀ y ∈ (NBar.sylowImage F Q : Subgroup (NBar.Q F)),
          ((NBar.ρ F y w₁ : ↥F) : G) ∈ D.A := by
        intro y hy
        rw [NBar.coe_sylowImage] at hy
        obtain ⟨yN, hyQ, rfl⟩ := hy
        have hyT : (yN : G) ∈ (T : Subgroup G) := by
          have : yN ∈ (Q : Subgroup _) := hyQ
          rw [hQ, mem_subgroupOf] at this
          exact this
        rw [hval]
        exact (mem_normalizer_iff.1 (D.T_le_normalizer_A hyT) a₁).1 ha₁
      set St : Subgroup (NBar.Q F) := (MulAction.stabilizer (MulAut ↥F) w₁).comap (NBar.ρ F)
        with hSt_def
      have hmemSt : ∀ g : NBar.Q F, g ∈ St ↔ NBar.ρ F g w₁ = w₁ := fun g => Iff.rfl
      have hOmove : ¬ pPrimeCore 2 (NBar.Q F) ≤ St := by
        intro hle
        apply hxA
        obtain ⟨s', hs', o, ho, hso⟩ := Normalizer.exists_mul_of_hasNormalPComplement
          (NBar.sylowImage F Q) hnc (NBar.π F ⟨x, hxN⟩)
        have h1 : NBar.ρ F (NBar.π F ⟨x, hxN⟩) w₁ = NBar.ρ F s' w₁ := by
          rw [hso, map_mul, MulAut.mul_apply, (hmemSt o).1 (hle ho)]
        have h2 := hDA s' hs'
        rw [← h1, hval] at h2
        exact h2
      have hx01 : NBar.ρ F x₀ w₁ ≠ w₁ ∨ NBar.ρ F x₁ w₁ ≠ w₁ := by
        by_contra hcon
        push Not at hcon
        apply hOmove
        rw [hcore]
        exact sup_le (zpowers_le.2 ((hmemSt x₀).2 hcon.1)) (zpowers_le.2 ((hmemSt x₁).2 hcon.2))
      have hne : pPrimeCore 2 (NBar.Q F) ≠ ⊥ := fun h' => hOmove (h' ▸ bot_le)
      have hx₀O : x₀ ∈ pPrimeCore 2 (NBar.Q F) := by rw [hcore]; exact mem_sup_left (mem_zpowers _)
      have hx₁O : x₁ ∈ pPrimeCore 2 (NBar.Q F) := by
        rw [hcore]; exact mem_sup_right (mem_zpowers _)
      refine ⟨?_, fun hF₂ => ?_⟩
      · rcases hx01 with h₀ | h₁
        · exact hnew x₀ (Normalizer.odd_orderOf_of_mem_pPrimeCore hx₀O) h₀ (Or.inl hc₀.symm)
        · exact hnew x₁ (Normalizer.odd_orderOf_of_mem_pPrimeCore hx₁O) h₁ (Or.inr hc₁.symm)
      · obtain ⟨t', ht'N, ht'2, ht'T₁⟩ := D.exists_tprime rfl hF₂
        have h11 := hL11 hne t' ht'N ht'2 ht'T₁
        have ht'N' := (mem_inf.1 ht'N).2
        have hodd : oddCent F = (fixV (zpowers (NBar.ρ F x₀)) ⊓
            fixV (zpowers (NBar.ρ F x₁))).map F.subtype := by
          ext y
          constructor
          · intro hy
            refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
            exact h11.mem_fix_iff.2 ((mem_oddCent_iff hnc ⟨y, hy.1⟩).1 hy)
          · rintro ⟨v, hv, rfl⟩
            exact (mem_oddCent_iff hnc v).2 (h11.mem_fix_iff.1 hv)
        rw [hodd]
        rcases hx01 with h₀ | h₁
        · exact (D.final_core hcen hF hd₀B₀ hd₀N hd₁B₁ hd₁N ht'N' ht'T₁ h11 ha₁ ha₁1 ha₁a
            h₀).symm
        ·
          have hτ : NBar.π F ⟨t', ht'N'⟩ * NBar.π F ⟨t', ht'N'⟩ = 1 := by
            rw [← map_mul]
            have : (⟨t', ht'N'⟩ : ↥(normalizer (F : Set G))) * ⟨t', ht'N'⟩ = 1 :=
              Subtype.ext ht'2
            rw [this, map_one]
          have ht'T₁s : t' * D.swap.t⁻¹ ∈ D.swap.T₁ := by
            rw [FooteCore.swap_T₁]
            exact ht'T₁
          have := D.swap.final_core hcen hF hd₁B₁ hd₁N hd₀B₀ hd₀N ht'N' ht'T₁s (h11.swap hτ)
            ha₁ ha₁1 ha₁a h₁
          rw [FooteCore.swap_Astar, inf_comm] at this
          exact this.symm
    ·
      refine ⟨?_, fun ⟨h, hh, hFh⟩ => absurd hFh (hnF₂ h hh)⟩
      obtain ⟨x₀, hx₀3, hx₀c, hx₀m⟩ := hSig w₁ (mem_sup_left ha₁) ⟨_, hxmove⟩
      exact hnew x₀ (by rw [hx₀3]; decide) hx₀m (Or.inl hx₀c)
  have hx2 : g * a₁ * g⁻¹ * (g * a₁ * g⁻¹) = 1 := by
    calc g * a₁ * g⁻¹ * (g * a₁ * g⁻¹) = g * (a₁ * a₁) * g⁻¹ := by group
      _ = 1 := by rw [D.mul_self_of_two ha₁, mul_one, mul_inv_cancel]
  obtain ⟨F, hFT₁, hFab, hFcard, hgF⟩ := D.exists_elem64_of_mem_T₁ (hL42 ha₁ ha₁1 ha₁a g hgT) hx2
  have hF : IsE64 (T : Subgroup G) F := ⟨hFT₁.trans D.T₁_le_T, hFab, hFcard⟩
  obtain ⟨x', hx'N, hx'F, hx'A⟩ := hnorm hF hgF hgA
  obtain ⟨⟨x'', F', hF', ⟨h, hh, hF'h⟩, hx''F, hx''A⟩, -⟩ := hstep hF hx'N hx'F hx'A
  obtain ⟨x₃, hx₃N, hx₃F, hx₃A⟩ := hnorm hF' hx''F hx''A
  refine ⟨h, hh, ?_⟩
  rw [← hF'h]
  exact (hstep hF' hx₃N hx₃F hx₃A).2 ⟨h, hh, hF'h⟩

end FooteCore

end CFSG.CGT.Foote81L6

module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EConj

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec5E

open Sec7 Sec8 T2M

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace Ctx

variable (C : Ctx S F T₁)

theorem T₂_le_N : C.D.T₂ ≤ normalizer (C.D.T₂ : Set X) := le_normalizer

theorem w₂_mem_N : C.D.w₂ ∈ normalizer (C.D.T₂ : Set X) := by
  rw [mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨a, rfl⟩ := C.exists_ι hb
    rw [C.w₂_conj]; exact C.ι_mem_T₂ _
  · intro hb
    obtain ⟨a, ha⟩ := C.exists_ι hb
    have h : b = C.D.w₂⁻¹ * C.ι a * C.D.w₂ := by rw [ha]; group
    rw [h, C.w₂_inv]
    have := C.w₂_conj a
    rw [C.w₂_inv] at this
    rw [this]; exact C.ι_mem_T₂ _

theorem R_le_N : C.D.R ≤ normalizer (C.D.T₂ : Set X) := by
  rw [C.D.R_eq]; exact sup_le C.T₂_le_N (zpowers_le.mpr C.w₂_mem_N)

theorem w₂_mem_R : C.D.w₂ ∈ C.D.R := by rw [C.D.R_eq]; exact mem_sup_right (mem_zpowers _)

theorem T₂_le_R : C.D.T₂ ≤ C.D.R := C.D.T₂_le

theorem mem_R_cases {r : X} (hr : r ∈ C.D.R) : r ∈ C.D.T₂ ∨ r * C.D.w₂⁻¹ ∈ C.D.T₂ := by
  rw [C.D.R_eq] at hr
  exact mem_or_of_mem_sup_zpowers C.w₂_mem_N (by rw [pow_two, C.w₂_mul_w₂]; exact one_mem _) hr

theorem mem_E₁_of_centralizer {P : Subgroup X} (hP : IsPGroup 2 P) {c : X} (hcP : c ∈ P)
    (hc : c ∈ centralizer (C.D.T₂ : Set X)) : c ∈ F.E₁ := by
  have hE : F.E₁ ≤ C.D.T₂ := E₁_le_T.trans C.T_le_T₂
  refine C.D.le_E (zpowers c) (hP.to_le (zpowers_le.mpr hcP)) ?_ (mem_zpowers c)
  rw [zpowers_le]
  exact centralizer_le hE hc

@[expose] noncomputable def CN : Subgroup (normalizer (C.D.T₂ : Set X)) :=
  (centralizer (C.D.T₂ : Set X)).subgroupOf (normalizer (C.D.T₂ : Set X))

instance CN_normal : C.CN.Normal := by
  constructor
  intro c hc n
  rw [CN, mem_subgroupOf] at hc ⊢
  rw [mem_centralizer_iff] at hc ⊢
  intro a ha
  have hn := n.2
  have ha' : (n : X)⁻¹ * a * n ∈ C.D.T₂ := by
    have := conj_mem_of_mem_normalizer (inv_mem hn) ha
    rwa [inv_inv] at this
  have h := hc _ ha'
  have key : a * ((n : X) * c * (n : X)⁻¹) = ((n : X) * c * (n : X)⁻¹) * a := by
    calc a * ((n : X) * c * (n : X)⁻¹) = n * ((n : X)⁻¹ * a * n * c) * (n : X)⁻¹ := by group
      _ = n * (c * ((n : X)⁻¹ * a * n)) * (n : X)⁻¹ := by rw [h]
      _ = ((n : X) * c * (n : X)⁻¹) * a := by group
  simpa using key

theorem isPGroup_quot (G : GD C) : IsPGroup 2 (normalizer (C.D.T₂ : Set X) ⧸ C.CN) := by
  intro q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  refine ⟨a, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, CN, mem_subgroupOf, mem_centralizer_iff]
  intro b hb
  have hnm : ((n : X) ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← Subgroup.coe_pow, ← hord, pow_orderOf_eq_one, Subgroup.coe_one]
  have h := G.centralizes_of_odd (pow_mem n.2 _) hm hnm hb
  simp only [Subgroup.coe_pow]
  calc b * (n : X) ^ 2 ^ a = ((n : X) ^ 2 ^ a * b * ((n : X) ^ 2 ^ a)⁻¹) * (n : X) ^ 2 ^ a := by
        rw [h]
    _ = (n : X) ^ 2 ^ a * b := by group

end Ctx

structure R2D (C : Ctx S F T₁) where
  G : GD C
  R₂ : Subgroup X
  isPGroup : IsPGroup 2 R₂
  le_N : R₂ ≤ normalizer (C.D.T₂ : Set X)
  R_le : C.D.R ≤ R₂
  maximal : ∀ P : Subgroup X, IsPGroup 2 P → R₂ ≤ P → P ≤ normalizer (C.D.T₂ : Set X) → P = R₂
  g : X
  g_mem : g ∈ R₂
  hσ : ∀ a, g * C.ι a * g⁻¹ = C.ι (G.p.sig a)
  hσinv : ∀ a, g⁻¹ * C.ι a * g = C.ι (G.p.sigInv a)
  g_sq_mem : g * g ∈ C.D.T₂
  g_sq_not : g * g ∉ S.data.T

namespace Ctx

variable (C : Ctx S F T₁)

theorem exists_r2D : Nonempty (R2D C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨G⟩ := C.exists_gD
  set N := normalizer (C.D.T₂ : Set X) with hN
  have hRp : IsPGroup 2 (C.D.R.subgroupOf N) :=
    C.D.isPGroup_R.comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  set R₂ : Subgroup X := (P : Subgroup N).map N.subtype with hR₂
  have hR₂p : IsPGroup 2 R₂ := P.isPGroup'.map _
  have hR₂N : R₂ ≤ N := map_subtype_le _
  have hRR₂ : C.D.R ≤ R₂ := fun r hr => ⟨⟨r, C.R_le_N hr⟩, hRP (mem_subgroupOf.mpr hr), rfl⟩
  have hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → R₂ ≤ Q → Q ≤ N → Q = R₂ := by
    intro Q hQ hR₂Q hQN
    have hQ' : IsPGroup 2 (Q.subgroupOf N) := hQ.comap_of_injective _ (subtype_injective _)
    have hPQ : (P : Subgroup N) ≤ Q.subgroupOf N := fun n hn =>
      mem_subgroupOf.mpr (hR₂Q ⟨n, hn, rfl⟩)
    have heq := P.is_maximal' hQ' hPQ
    refine le_antisymm (fun q hq => ?_) hR₂Q
    have : (⟨q, hQN hq⟩ : N) ∈ Q.subgroupOf N := mem_subgroupOf.mpr hq
    rw [heq] at this
    exact ⟨_, this, rfl⟩
  have hgN : G.g ∈ N := by
    rw [hN, mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      obtain ⟨a, rfl⟩ := C.exists_ι hb
      rw [G.hσ]; exact C.ι_mem_T₂ _
    · intro hb
      obtain ⟨a, ha⟩ := C.exists_ι hb
      have h : b = G.g⁻¹ * C.ι a * G.g := by rw [ha]; group
      rw [h, G.hσinv]; exact C.ι_mem_T₂ _
  set π := QuotientGroup.mk' C.CN with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set P' := P.mapSurjective hπs with hP'
  have hP'top : (P' : Subgroup (N ⧸ C.CN)) = ⊤ :=
    (P'.is_maximal' ((C.isPGroup_quot G).to_subgroup ⊤) le_top).symm
  have hmem : π ⟨G.g, hgN⟩ ∈ (P' : Subgroup (N ⧸ C.CN)) := by rw [hP'top]; exact mem_top _
  rw [hP', Sylow.coe_mapSurjective] at hmem
  obtain ⟨r, hrP, hr⟩ := hmem
  have hrc : (r : X)⁻¹ * G.g ∈ centralizer (C.D.T₂ : Set X) := by
    have := (QuotientGroup.eq (s := C.CN)).mp hr
    rw [CN, mem_subgroupOf] at this
    simpa using this
  set g' : X := (r : X) with hg'
  have hg'R₂ : g' ∈ R₂ := ⟨r, hrP, rfl⟩
  have hact : ∀ b ∈ C.D.T₂, g' * b * g'⁻¹ = G.g * b * G.g⁻¹ := by
    intro b hb
    have hc := mem_centralizer_iff.mp hrc b hb
    calc g' * b * g'⁻¹ = g' * (b * (g'⁻¹ * G.g)) * (g'⁻¹ * G.g)⁻¹ * g'⁻¹ := by group
      _ = g' * ((g'⁻¹ * G.g) * b) * (g'⁻¹ * G.g)⁻¹ * g'⁻¹ := by rw [hc]
      _ = G.g * b * G.g⁻¹ := by group
  have hact' : ∀ b ∈ C.D.T₂, g'⁻¹ * b * g' = G.g⁻¹ * b * G.g := by
    intro b hb
    have hc := mem_centralizer_iff.mp hrc
    have hb' : G.g⁻¹ * b * G.g ∈ C.D.T₂ := by
      rw [← C.ι_ιinv hb, G.hσinv]; exact C.ι_mem_T₂ _
    have h1 := hc _ hb'
    calc g'⁻¹ * b * g' = (g'⁻¹ * G.g) * (G.g⁻¹ * b * G.g) * (g'⁻¹ * G.g)⁻¹ := by group
      _ = (G.g⁻¹ * b * G.g) * (g'⁻¹ * G.g) * (g'⁻¹ * G.g)⁻¹ := by rw [h1]
      _ = G.g⁻¹ * b * G.g := by group
  have hg2 : (G.g * G.g)⁻¹ * (g' * g') ∈ F.E₁ := by
    refine C.mem_E₁_of_centralizer hR₂p (mul_mem (inv_mem (hRR₂ (C.T₂_le_R G.g_sq_mem)))
      (mul_mem hg'R₂ hg'R₂)) (mem_centralizer_iff.mpr fun b hb => ?_)
    have h3 : (g' * g') * b * (g' * g')⁻¹ = (G.g * G.g) * b * (G.g * G.g)⁻¹ := by
      calc (g' * g') * b * (g' * g')⁻¹ = g' * (g' * b * g'⁻¹) * g'⁻¹ := by group
        _ = G.g * (G.g * b * G.g⁻¹) * G.g⁻¹ := by
            rw [hact b hb, hact _ (C.conj_mem_T₂ G.g_mem hb)]
        _ = (G.g * G.g) * b * (G.g * G.g)⁻¹ := by group
    calc b * ((G.g * G.g)⁻¹ * (g' * g')) =
        (G.g * G.g)⁻¹ * ((G.g * G.g) * b * (G.g * G.g)⁻¹) * (g' * g') := by group
      _ = (G.g * G.g)⁻¹ * ((g' * g') * b * (g' * g')⁻¹) * (g' * g') := by rw [h3]
      _ = (G.g * G.g)⁻¹ * (g' * g') * b := by group
  have hE₁T : F.E₁ ≤ S.data.T := E₁_le_T
  refine ⟨⟨G, R₂, hR₂p, hR₂N, hRR₂, hmax, g', hg'R₂, fun a => ?_, fun a => ?_, ?_, ?_⟩⟩
  · rw [hact _ (C.ι_mem_T₂ a), G.hσ]
  · rw [hact' _ (C.ι_mem_T₂ a), G.hσinv]
  · have := mul_mem G.g_sq_mem (C.T_le_T₂ (hE₁T hg2))
    rwa [mul_inv_cancel_left] at this
  · intro h
    apply G.g_sq_not
    have := mul_mem h (inv_mem (hE₁T hg2))
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

end Ctx

theorem sw2_sw2 : ∀ a : T2M, sw2 (sw2 a) = a := by decide +kernel

theorem Zl_le_E : ∀ c ∈ Zl, InE1 c ∧ c ∈ E2l ∧ c ∈ E5l := by decide +kernel

theorem exists_sw2_E2 : ∃ e ∈ E2l, sw2 e ∉ E2l := by decide +kernel

theorem y_not_central : ∃ c : T2M, y * c ≠ c * y := by decide +kernel

theorem ty_mem_tEl : t * y ∈ tEl := by decide +kernel

theorem t_mem_tEl : t ∈ tEl := by decide +kernel

@[expose] def SfE (p : SigD) : Prop :=
  (∀ e : T2M, InE1 e → InE1 (p.sf e)) ∧ (∀ e ∈ E2l, p.sf e ∈ E2l) ∧ (∀ c ∈ Zl, c ∈ p.E6l)

instance (p : SigD) : Decidable (SfE p) := by unfold SfE; infer_instance

theorem sfE : ∀ p ∈ repList, SfE p := by decide +kernel

omit [Finite X] in
theorem mem_normalizer_of_conj_le' {H : Subgroup X} [Finite H] {n : X}
    (h : ∀ a ∈ H, n * a * n⁻¹ ∈ H) : n ∈ normalizer (H : Set X) := by
  refine mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · rintro _ ⟨a, ha, rfl⟩; exact h a ha
  · rw [card_map_of_injective (MulAut.conj n).injective]

namespace Ctx

variable (C : Ctx S F T₁)

@[expose] noncomputable def E₅ : Subgroup X := F.E₂.map (MulAut.conj C.D.w₂).toMonoidHom

theorem ι_mem_E₅_iff (a : T2M) : C.ι a ∈ C.E₅ ↔ a ∈ E5l := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have hbT : b ∈ C.D.T₂ := E₂_le_T.trans C.T_le_T₂ hb
    obtain ⟨b', rfl⟩ := C.exists_ι hbT
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hba
    rw [C.w₂_conj] at hba
    rw [← C.ι_injective hba]
    exact sw2_E2 b' ((C.ι_mem_E₂_iff b').mp hb)
  · intro ha
    refine ⟨C.ι (sw2 a), (C.ι_mem_E₂_iff _).mpr (sw2_E5 a ha), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [C.w₂_conj, sw2_sw2]

theorem E₅_le_T₂ : C.E₅ ≤ C.D.T₂ := by
  rintro _ ⟨b, hb, rfl⟩
  exact conj_mem_of_mem_normalizer C.w₂_mem_N (E₂_le_T.trans C.T_le_T₂ hb)

theorem card_E₅ : Nat.card C.E₅ = 16 := by
  rw [E₅, card_map_of_injective (MulAut.conj _).injective, card_E₂]

include C in
theorem conj_E₁_le {r : X} {K : Subgroup X} (hz : r * S.z * r⁻¹ ∈ K)
    (hy : r * F.yF * r⁻¹ ∈ K) (ht : r * S.t * r⁻¹ ∈ K) (hk : r * F.kF * r⁻¹ ∈ K) :
    F.E₁.map (MulAut.conj r).toMonoidHom ≤ K := by
  rw [Ctx.E₁_eq C, MonoidHom.map_closure, closure_le]
  rintro _ ⟨c, hc, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simpa [MulAut.conj_apply]

end Ctx

namespace R2D

variable {C : Ctx S F T₁} (B : R2D C)

@[expose] noncomputable def E₆ : Subgroup X := C.E₅.map (MulAut.conj B.g).toMonoidHom

theorem ι_mem_E₆_iff (a : T2M) : C.ι a ∈ B.E₆ ↔ a ∈ B.G.p.E6l := by
  constructor
  · rintro ⟨b, hb, hba⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hba
    have hb' : b = C.ι (B.G.p.sigInv a) := by rw [← B.hσinv, ← hba]; group
    rw [hb'] at hb
    simp only [SigD.E6l, List.mem_map]
    exact ⟨_, (C.ι_mem_E₅_iff _).mp hb, SigD.sigInvOk B.G.p B.G.hp a⟩
  · intro ha
    simp only [SigD.E6l, List.mem_map] at ha
    obtain ⟨e, he, rfl⟩ := ha
    refine ⟨C.ι e, (C.ι_mem_E₅_iff e).mpr he, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [B.hσ]

theorem card_E₆ : Nat.card B.E₆ = 16 := by
  rw [E₆, card_map_of_injective (MulAut.conj _).injective, C.card_E₅]

theorem g_mem_N : B.g ∈ normalizer (C.D.T₂ : Set X) := B.le_N B.g_mem

theorem w₂_mem_R₂ : C.D.w₂ ∈ B.R₂ := B.R_le C.w₂_mem_R

theorem mem_R_of {r : X} (hr : r ∈ B.R₂) (hn : r ∈ normalizer (F.E₁ : Set X)) : r ∈ C.D.R := by
  have := C.D.R_maximal (B.R₂ ⊓ normalizer (F.E₁ : Set X)) (B.isPGroup.to_le inf_le_left)
    (le_inf B.R_le C.D.R_le) inf_le_right
  rw [← this]; exact ⟨hr, hn⟩

theorem card_conj_E₁ (r : X) : Nat.card (F.E₁.map (MulAut.conj r).toMonoidHom) = 16 := by
  rw [card_map_of_injective (MulAut.conj r).injective, Ctx.card_E₁]

theorem conj_E₁_eq {r : X} {K : Subgroup X} (hK : Nat.card K = 16)
    (h : F.E₁.map (MulAut.conj r).toMonoidHom ≤ K) : F.E₁.map (MulAut.conj r).toMonoidHom = K :=
  Subgroup.eq_of_le_of_card_ge h (by rw [hK, card_conj_E₁])

theorem model_t_y : t * y = y * t := by decide +kernel

theorem conj_E₁_cases {r : X} (hr : r ∈ B.R₂) :
    F.E₁.map (MulAut.conj r).toMonoidHom = F.E₁ ∨ F.E₁.map (MulAut.conj r).toMonoidHom = F.E₂ ∨
      F.E₁.map (MulAut.conj r).toMonoidHom = C.E₅ ∨
        F.E₁.map (MulAut.conj r).toMonoidHom = B.E₆ := by
  have hrN := B.le_N hr
  set ν := C.conjM r hrN with hν
  have hι : ∀ a, r * C.ι a * r⁻¹ = C.ι (ν a) := fun a => (C.ι_conjM hrN a).symm
  have hinj : Function.Injective ν := by
    intro a b hab
    have := congrArg C.ι hab
    rw [← hι, ← hι] at this
    exact C.ι_injective (by simpa using this)
  have hsurj : Function.Surjective ν := Finite.injective_iff_surjective.mp hinj
  have hZ : ∀ c ∈ Zl, ν c ∈ Zl := by
    intro c hc
    refine mem_Zl_of_central _ fun b => ?_
    obtain ⟨b', rfl⟩ := hsurj b
    rw [← map_mul, ← map_mul, central_of_mem_Zl c hc b']
  have hS : ∀ a ∈ B.G.p.S16, ν a ∈ B.G.p.S16 := by
    intro a ha
    obtain ⟨ha2, ha1⟩ := s16Inv B.G.p B.G.hp a ha
    have hc := conjTo_conj (B.G.conj_S16 ha) r
    rw [hι] at hc
    refine (B.G.conjTo_iff (by rw [← map_mul, ha2, map_one]) (fun h => ha1 ?_)).mp hc
    exact hinj (h.trans (map_one ν).symm)
  have hmemS : ∀ e ∈ tEl, e ∈ B.G.p.S16 := fun e he => by
    simp only [SigD.S16, List.mem_append]; exact Or.inl (Or.inl (Or.inl he))
  have ha := hS t (hmemS t t_mem_tEl)
  have hab : ν t * ν y ∈ B.G.p.S16 := by rw [← map_mul]; exact hS _ (hmemS _ ty_mem_tEl)
  have hcomm : ν t * ν y = ν y * ν t := by rw [← map_mul, ← map_mul, model_t_y]
  have hb2 : ν y * ν y = 1 := by rw [← map_mul, Ctx.model_y_y, map_one]
  have hbZ : ν y ∉ Zl := by
    intro h
    obtain ⟨c, hc⟩ := y_not_central
    apply hc
    apply hinj
    rw [map_mul, map_mul]
    exact central_of_mem_Zl _ h _
  have hzZ := hZ z (by decide +kernel)
  have hkZ := hZ k (by decide +kernel)
  have hz' : r * S.z * r⁻¹ = C.ι (ν z) := by rw [← hι, C.ι_z]
  have hy' : r * F.yF * r⁻¹ = C.ι (ν y) := by rw [← hι, C.ι_y]
  have ht' : r * S.t * r⁻¹ = C.ι (ν t) := by rw [← hι, C.ι_t]
  have hk' : r * F.kF * r⁻¹ = C.ι (ν k) := by rw [← hι, C.ι_k]
  rcases SigD.orbitCases B.G.p B.G.hp _ ha _ hab hcomm hb2 hbZ with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine conj_E₁_eq Ctx.card_E₁ (C.conj_E₁_le ?_ ?_ ?_ ?_) <;>
      simp only [hz', hy', ht', hk', C.ι_mem_E₁_iff]
    exacts [(Zl_le_E _ hzZ).1, h2, h1, (Zl_le_E _ hkZ).1]
  · right; left
    refine conj_E₁_eq Ctx.card_E₂ (C.conj_E₁_le ?_ ?_ ?_ ?_) <;>
      simp only [hz', hy', ht', hk', C.ι_mem_E₂_iff]
    exacts [(Zl_le_E _ hzZ).2.1, h2, h1, (Zl_le_E _ hkZ).2.1]
  · right; right; left
    refine conj_E₁_eq C.card_E₅ (C.conj_E₁_le ?_ ?_ ?_ ?_) <;>
      simp only [hz', hy', ht', hk', C.ι_mem_E₅_iff]
    exacts [(Zl_le_E _ hzZ).2.2, h2, h1, (Zl_le_E _ hkZ).2.2]
  · right; right; right
    have hZ6 := (sfE B.G.p B.G.hp).2.2
    refine conj_E₁_eq B.card_E₆ (C.conj_E₁_le ?_ ?_ ?_ ?_) <;>
      simp only [hz', hy', ht', hk', B.ι_mem_E₆_iff]
    exacts [hZ6 _ hzZ, h2, h1, hZ6 _ hkZ]


theorem conj_E₁_le_of {r : X} {K : Subgroup X} (h : ∀ a : T2M, InE1 a → r * C.ι a * r⁻¹ ∈ K) :
    F.E₁.map (MulAut.conj r).toMonoidHom ≤ K :=
  C.conj_E₁_le (by rw [← C.ι_z]; exact h _ (by decide +kernel))
    (by rw [← C.ι_y]; exact h _ (by decide +kernel))
    (by rw [← C.ι_t]; exact h _ (by decide +kernel))
    (by rw [← C.ι_k]; exact h _ (by decide +kernel))

theorem conj_g_E₁ : F.E₁.map (MulAut.conj B.g).toMonoidHom = F.E₂ :=
  conj_E₁_eq Ctx.card_E₂ (conj_E₁_le_of fun a ha => by
    rw [B.hσ, C.ι_mem_E₂_iff]; exact (SigD.eAct B.G.p B.G.hp).1 a ha)

theorem conj_w₂g_E₁ : F.E₁.map (MulAut.conj (C.D.w₂ * B.g)).toMonoidHom = C.E₅ :=
  conj_E₁_eq C.card_E₅ (conj_E₁_le_of fun a ha => by
    rw [show C.D.w₂ * B.g * C.ι a * (C.D.w₂ * B.g)⁻¹ =
      C.D.w₂ * (B.g * C.ι a * B.g⁻¹) * C.D.w₂⁻¹ by group, B.hσ, C.w₂_conj, C.ι_mem_E₅_iff]
    exact sw2_E2 _ ((SigD.eAct B.G.p B.G.hp).1 a ha))

theorem conj_gw₂g_E₁ : F.E₁.map (MulAut.conj (B.g * C.D.w₂ * B.g)).toMonoidHom = B.E₆ :=
  conj_E₁_eq B.card_E₆ (conj_E₁_le_of fun a ha => by
    rw [show B.g * C.D.w₂ * B.g * C.ι a * (B.g * C.D.w₂ * B.g)⁻¹ =
      B.g * (C.D.w₂ * (B.g * C.ι a * B.g⁻¹) * C.D.w₂⁻¹) * B.g⁻¹ by group, B.hσ, C.w₂_conj,
      B.hσ, B.ι_mem_E₆_iff]
    simp only [SigD.E6l, List.mem_map]
    exact ⟨_, sw2_E2 _ ((SigD.eAct B.G.p B.G.hp).1 a ha), rfl⟩)

omit [Finite X] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup X} {r s : X}
    (h : H.map (MulAut.conj r).toMonoidHom = H.map (MulAut.conj s).toMonoidHom) :
    s⁻¹ * r ∈ normalizer (H : Set X) := by
  apply mem_normalizer_of_map_eq
  have h1 : (MulAut.conj (s⁻¹ * r)).toMonoidHom =
      (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj r).toMonoidHom := by
    ext a; simp [MulAut.conj_apply, mul_assoc]
  have h2 : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom = MonoidHom.id X := by
    ext a; simp [MulAut.conj_apply, mul_assoc]
  rw [h1, ← Subgroup.map_map, h, Subgroup.map_map, h2, Subgroup.map_id]

theorem mem_cases {r : X} (hr : r ∈ B.R₂) : r ∈ C.D.R ∨ B.g⁻¹ * r ∈ C.D.R ∨
    (C.D.w₂ * B.g)⁻¹ * r ∈ C.D.R ∨ (B.g * C.D.w₂ * B.g)⁻¹ * r ∈ C.D.R := by
  have hw₂g : C.D.w₂ * B.g ∈ B.R₂ := mul_mem B.w₂_mem_R₂ B.g_mem
  have hgw₂g : B.g * C.D.w₂ * B.g ∈ B.R₂ := mul_mem (mul_mem B.g_mem B.w₂_mem_R₂) B.g_mem
  have hmem : ∀ s ∈ B.R₂, F.E₁.map (MulAut.conj r).toMonoidHom =
      F.E₁.map (MulAut.conj s).toMonoidHom → s⁻¹ * r ∈ C.D.R := fun s hs h =>
    B.mem_R_of (mul_mem (inv_mem hs) hr) (mem_normalizer_of_map_conj_eq h)
  rcases B.conj_E₁_cases hr with h | h | h | h
  · left
    have h1 : F.E₁.map (MulAut.conj (1 : X)).toMonoidHom = F.E₁ := by
      ext a; simp
    have := hmem 1 (one_mem _) (by rw [h, h1])
    simpa using this
  · exact Or.inr (Or.inl (hmem _ B.g_mem (by rw [h, B.conj_g_E₁])))
  · exact Or.inr (Or.inr (Or.inl (hmem _ hw₂g (by rw [h, B.conj_w₂g_E₁]))))
  · exact Or.inr (Or.inr (Or.inr (hmem _ hgw₂g (by rw [h, B.conj_gw₂g_E₁]))))

@[expose] noncomputable def w₂₂ : X := B.g * C.D.w₂ * B.g⁻¹

@[expose] noncomputable def q : X := B.w₂₂ * C.D.w₂

theorem w₂₂_conj (a : T2M) : B.w₂₂ * C.ι a * B.w₂₂⁻¹ = C.ι (B.G.p.sw22 a) := by
  rw [w₂₂, show B.g * C.D.w₂ * B.g⁻¹ * C.ι a * (B.g * C.D.w₂ * B.g⁻¹)⁻¹ =
    B.g * (C.D.w₂ * (B.g⁻¹ * C.ι a * B.g) * C.D.w₂⁻¹) * B.g⁻¹ by group, B.hσinv, C.w₂_conj,
    B.hσ]
  rfl

theorem q_conj (a : T2M) : B.q * C.ι a * B.q⁻¹ = C.ι (B.G.p.sq a) := by
  rw [q, show B.w₂₂ * C.D.w₂ * C.ι a * (B.w₂₂ * C.D.w₂)⁻¹ =
    B.w₂₂ * (C.D.w₂ * C.ι a * C.D.w₂⁻¹) * B.w₂₂⁻¹ by group, C.w₂_conj, B.w₂₂_conj]
  rfl

theorem f_conj (a : T2M) : (B.q * B.q) * C.ι a * (B.q * B.q)⁻¹ = C.ι (B.G.p.sf a) := by
  rw [show B.q * B.q * C.ι a * (B.q * B.q)⁻¹ = B.q * (B.q * C.ι a * B.q⁻¹) * B.q⁻¹ by group,
    B.q_conj, B.q_conj]
  rfl

theorem w₂₂_mem : B.w₂₂ ∈ B.R₂ := mul_mem (mul_mem B.g_mem B.w₂_mem_R₂) (inv_mem B.g_mem)

theorem q_mem : B.q ∈ B.R₂ := mul_mem B.w₂₂_mem B.w₂_mem_R₂

theorem f_mem_T₂ : B.q * B.q ∈ C.D.T₂ := by
  have hE := sfE B.G.p B.G.hp
  have hN1 : B.q * B.q ∈ normalizer (F.E₁ : Set X) := by
    refine mem_normalizer_of_conj_le' fun a ha => ?_
    obtain ⟨a', rfl⟩ := C.exists_ι (Ctx.E₁_le_T.trans C.T_le_T₂ ha)
    rw [B.f_conj, C.ι_mem_E₁_iff]
    exact hE.1 a' ((C.ι_mem_E₁_iff a').mp ha)
  have hR := B.mem_R_of (mul_mem B.q_mem B.q_mem) hN1
  rcases C.mem_R_cases hR with h | h
  · exact h
  · exfalso
    obtain ⟨τ, hτ⟩ := C.exists_ι h
    obtain ⟨e, he, hse⟩ := exists_sw2_E2
    have h1 : (B.q * B.q) * C.ι e * (B.q * B.q)⁻¹ ∈ F.E₂ := by
      rw [B.f_conj, C.ι_mem_E₂_iff]; exact hE.2.1 e he
    have h2 : B.q * B.q = C.ι τ * C.D.w₂ := by rw [hτ]; group
    rw [h2, show C.ι τ * C.D.w₂ * C.ι e * (C.ι τ * C.D.w₂)⁻¹ =
      C.ι τ * (C.D.w₂ * C.ι e * C.D.w₂⁻¹) * (C.ι τ)⁻¹ by group, C.w₂_conj, ← map_inv,
      ← map_mul, ← map_mul, C.ι_mem_E₂_iff] at h1
    have h3 := conj_E2 τ⁻¹ _ h1
    rw [show τ⁻¹ * (τ * sw2 e * τ⁻¹) * τ⁻¹⁻¹ = sw2 e by group] at h3
    exact hse h3

theorem mem_repList' : B.G.p ∈ repList' ∧ B.G.p.InN (C.ιinv (B.q * B.q)) := by
  refine SigD.innerF B.G.p B.G.hp _ fun g _ => C.ι_injective ?_
  rw [← B.f_conj, map_mul, map_mul, map_inv, C.ι_ιinv B.f_mem_T₂]

end R2D

end Sec5E

end CFSG.ComponentClassification.HSFLit

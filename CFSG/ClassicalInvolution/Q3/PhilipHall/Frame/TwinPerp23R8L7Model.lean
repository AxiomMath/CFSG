module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Abs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
  CFSG.ClassicalInvolution.Q3.TC.Thin

section Predicates

@[expose] def ModelLayer (k : ℕ) (𝒜 : Set (Finset (Fin k))) (a : AE.AEQ k) : Prop :=
  a ≠ 1 ∧ a * a = 1 ∧ a ∈ Ea (aeMembers k 𝒜) a ∧ ¬ Group.IsSolvable ↥(Ea (aeMembers k 𝒜) a)

@[expose] def ModelNoLayer (k : ℕ) (𝒜 : Set (Finset (Fin k))) (H : Subgroup (AE.AEQ k)) : Prop :=
  ∀ a ∈ H, ¬ ModelLayer k 𝒜 a

@[expose] def AE7LayerOrbit : Prop :=
  ∀ (α : Finset (Fin 7)) (h : α.card = 4) (a₁ a₂ : AE.AEQ 7),
    a₁ ∈ (AE.aeSub 7).map (AE.mkQ 7) → a₂ ∈ (AE.aeSub 7).map (AE.mkQ 7) →
    ModelLayer 7 Set.univ a₁ → ModelLayer 7 Set.univ a₂ →
    (∀ (b : Bool), ∀ x ∈ AE.memBar α h b, a₁ * x = x * a₁) →
    (∀ (b : Bool), ∀ x ∈ AE.memBar α h b, a₂ * x = x * a₂) →
    ∃ w ∈ (AE.aeSub 7).map (AE.mkQ 7), Odd (orderOf w) ∧
      (∀ (b : Bool), ∀ x ∈ AE.memBar α h b, w * x = x * w) ∧ w * a₁ * w⁻¹ = a₂

end Predicates

section Transfer

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem psi_ker_central {A : Type} [Group A] (hgen : pSpan Φ = ⊤) (φ : ↥(pSpan Φ) →* A)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ)) {x : G} (hx : (φ.comp (toPSpan hgen)) x = 1) :
    x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : (toPSpan hgen x : ↥(pSpan Φ)) ∈ φ.ker := hx
  have h2 := Subgroup.mem_center_iff.mp (hker h1) (toPSpan hgen y)
  exact congrArg Subtype.val h2

theorem modelLayer_of_layer (F : TwinDisc.ExitO2.Q8Fam G Φ) {k : ℕ} (hk : 5 ≤ k)
    {𝒜 : Set (Finset (Fin k))} (φ : ↥(pSpan Φ) →* AE.AEQ k)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan Φ))
    (hlabel : ∀ L ∈ Φ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map φ = AE.memBar α h b) {a : G} (ha2 : a * a = 1)
    (hanc : a ∉ Subgroup.center G) (haE : a ∈ Ea Φ a) (hns : ¬ Group.IsSolvable ↥(Ea Φ a)) :
    ModelLayer k 𝒜 ((φ.comp (toPSpan F.gen)) a) := by
  have hkc : ∀ x : G, (φ.comp (toPSpan F.gen)) x = 1 → x ∈ Subgroup.center G := fun x hx =>
    psi_ker_central F.gen φ hker hx
  have hEa := Ea_map_model F hk φ hker hlabel hsurj a
  unfold ModelLayer
  refine ⟨fun h => hanc (hkc a h), ?_, ?_, ?_⟩
  · rw [← map_mul, ha2, map_one]
  · rw [hEa]
    exact Subgroup.mem_map_of_mem _ haE
  · rw [hEa]
    exact not_isSolvable_map _ hkc hns

theorem twin_labels (F : TwinDisc.ExitO2.Q8Fam G Φ) (I : AEIdent Φ 7) {K K' : Subgroup G} (hK : K ∈ Φ)
    (hK' : K' ∈ Φ) (hne : K' ≠ K) {zb : G} (hzb : IsUniqueInvolution K zb)
    (hzb' : IsUniqueInvolution K' zb) :
    ∃ (α : Finset (Fin 7)) (h : α.card = 4) (b : Bool),
      K.map (I.φ.comp (toPSpan F.gen)) = AE.memBar α h b ∧
      K'.map (I.φ.comp (toPSpan F.gen)) = AE.memBar α h (!b) := by
  obtain ⟨hinj, heq, -⟩ := psi_props F (by norm_num : 5 ≤ 7) I.φ I.ker_le I.label
  obtain ⟨α, h, b, hl⟩ := I.label K hK
  obtain ⟨β, h', c, hl'⟩ := I.label K' hK'
  have hl1 : K.map (I.φ.comp (toPSpan F.gen)) = AE.memBar α h b :=
    (map_toPSpan I.φ F.gen hK).trans hl
  have hl2 : K'.map (I.φ.comp (toPSpan F.gen)) = AE.memBar β h' c :=
    (map_toPSpan I.φ F.gen hK').trans hl'
  have hz : ∀ {L : Subgroup G}, L ∈ Φ → ∀ {γ : Finset (Fin 7)} {hγ : γ.card = 4} {d : Bool},
      L.map (I.φ.comp (toPSpan F.gen)) = AE.memBar γ hγ d → IsUniqueInvolution L zb →
        (I.φ.comp (toPSpan F.gen)) zb = AE.zBar γ hγ := by
    intro L hL γ hγ d hLd hu
    have hmem : (I.φ.comp (toPSpan F.gen)) zb ∈ AE.memBar γ hγ d := by
      rw [← hLd]
      exact ⟨zb, hu.mem, rfl⟩
    have hsq : (I.φ.comp (toPSpan F.gen)) zb * (I.φ.comp (toPSpan F.gen)) zb = 1 := by
      rw [← map_mul, hu.sq, map_one]
    rcases AE.eq_of_mem_memBar_mul_self (by norm_num : 5 ≤ 7) hmem hsq with h1 | h1
    · exact absurd (hinj L hL zb hu.mem h1) hu.ne_one
    · exact h1
  have e1 := hz hK hl1 hzb
  have e2 := hz hK' hl2 hzb'
  have hβα : β = α := AE.eq_of_zBar_eq (by norm_num : (7 : ℕ) ≠ 8) (e2.symm.trans e1)
  subst hβα
  have hcb : c = !b := by
    by_contra hcb
    have hcb' : c = b := by
      revert hcb
      cases c <;> cases b <;> simp
    subst hcb'
    exact hne (heq K' hK' K hK (hl2.trans hl1.symm))
  subst hcb
  exact ⟨β, h, b, hl1, hl2⟩

theorem exists_w_of_orbit (F : TwinDisc.ExitO2.Q8Fam G Φ) (I : AEIdent Φ 7) (Ho : AE7LayerOrbit)
    {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {zb : G}
    (hzb : IsUniqueInvolution K zb) (hzb' : IsUniqueInvolution K' zb) {a b : G} (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hanc : a ∉ Subgroup.center G) (hbnc : b ∉ Subgroup.center G)
    (haE : a ∈ Ea Φ a) (hbE : b ∈ Ea Φ b) (hna : ¬ Group.IsSolvable ↥(Ea Φ a))
    (hnb : ¬ Group.IsSolvable ↥(Ea Φ b)) (haK : ∀ x ∈ K, a * x = x * a)
    (haK' : ∀ x ∈ K', a * x = x * a) (hbK : ∀ x ∈ K, b * x = x * b)
    (hbK' : ∀ x ∈ K', b * x = x * b)
    (hcen : ∀ c ∈ Subgroup.center G, c ∈ Ea Φ b → c = 1) :
    ∃ w : G, (∀ x ∈ K, w * x = x * w) ∧ (∀ x ∈ K', w * x = x * w) ∧ w * a * w⁻¹ = b := by
  obtain ⟨hinj, heq, hk2⟩ := psi_props F (by norm_num : 5 ≤ 7) I.φ I.ker_le I.label
  obtain ⟨α, h, b₀, hlK, hlK'⟩ := twin_labels F I hK hK' hne hzb hzb'
  have hlabel : ∀ L ∈ Φ, ∃ α ∈ (Set.univ : Set (Finset (Fin 7))), ∃ (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Φ)).map I.φ = AE.memBar α h b := fun L hL => by
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨α, Set.mem_univ _, h, b, hlab⟩
  have hsurj : ∀ α ∈ (Set.univ : Set (Finset (Fin 7))), ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map I.φ = AE.memBar α h b := fun α _ h b => I.label_surj α h b
  have hma := modelLayer_of_layer F (by norm_num : 5 ≤ 7) I.φ I.ker_le hlabel hsurj ha2 hanc haE hna
  have hmb := modelLayer_of_layer F (by norm_num : 5 ≤ 7) I.φ I.ker_le hlabel hsurj hb2 hbnc hbE hnb
  have hrange : ∀ x : G, (I.φ.comp (toPSpan F.gen)) x ∈ (AE.aeSub 7).map (AE.mkQ 7) := fun x => by
    rw [← I.range_eq]
    exact ⟨_, rfl⟩
  have hcent : ∀ {c : G}, (∀ x ∈ K, c * x = x * c) → (∀ x ∈ K', c * x = x * c) →
      ∀ (d : Bool), ∀ y ∈ AE.memBar α h d,
        (I.φ.comp (toPSpan F.gen)) c * y = y * (I.φ.comp (toPSpan F.gen)) c := by
    intro c hcK hcK' d y hy
    have hd : d = b₀ ∨ d = !b₀ := by cases d <;> cases b₀ <;> simp
    rcases hd with rfl | rfl
    · rw [← hlK] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_mul, ← map_mul, hcK x hx]
    · rw [← hlK'] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_mul, ← map_mul, hcK' x hx]
  obtain ⟨wb, hwb, hodd, hwcent, hwconj⟩ := Ho α h _ _ (hrange a) (hrange b) hma hmb
    (hcent haK haK') (hcent hbK hbK')
  have hwr : wb ∈ (I.φ.comp (toPSpan F.gen)).range := by
    have hwb' : wb ∈ I.φ.range := by
      rw [I.range_eq]
      exact hwb
    obtain ⟨y, hy⟩ := hwb'
    refine ⟨(y : G), ?_⟩
    have hty : toPSpan F.gen (y : G) = y := Subtype.ext rfl
    show I.φ (toPSpan F.gen (y : G)) = wb
    rw [hty, hy]
  obtain ⟨w, hw, hwodd⟩ := exists_odd_lift _ hwr hodd
  have hcomm : ∀ {L : Subgroup G} {d : Bool}, L.map (I.φ.comp (toPSpan F.gen)) = AE.memBar α h d →
      ∀ x ∈ L, w * x = x * w := by
    intro L d hL x hx
    have hxm : (I.φ.comp (toPSpan F.gen)) x ∈ AE.memBar α h d := by
      rw [← hL]
      exact ⟨x, hx, rfl⟩
    have hψc : (I.φ.comp (toPSpan F.gen)) (w * x * w⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hw, hwcent d _ hxm]
      group
    have hcc := psi_ker_central F.gen I.φ I.ker_le hψc
    obtain ⟨j, hj⟩ := hk2 _ hψc
    have h1 := comm_eq_one_of_odd hwodd hcc ⟨j, hj⟩
    calc w * x = (w * x * w⁻¹ * x⁻¹) * (x * w) := by group
      _ = x * w := by rw [h1, one_mul]
  refine ⟨w, hcomm hlK, hcomm hlK', ?_⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : G, c₂ = (w * a * w⁻¹) * b⁻¹ := ⟨_, rfl⟩
  have hψc₂ : (I.φ.comp (toPSpan F.gen)) c₂ = 1 := by
    rw [hc₂, map_mul, map_mul, map_mul, map_inv, map_inv, hw, hwconj, mul_inv_cancel]
  have hc₂c : c₂ ∈ Subgroup.center G := psi_ker_central F.gen I.φ I.ker_le hψc₂
  have hgb : w * a * w⁻¹ = b * c₂ := by
    have hbc : b * c₂ = c₂ * b := Subgroup.mem_center_iff.mp hc₂c b
    rw [hbc, hc₂]
    group
  have hconj : w * a * w⁻¹ ∈ Ea Φ (w * a * w⁻¹) :=
    conj_mem_Ea (fun L hL g => F.hyp.conjInvariant g L hL) w a haE
  rw [hgb, Ea_mul_central Φ hc₂c] at hconj
  have hc₂E : c₂ ∈ Ea Φ b := by
    have h1 : b⁻¹ * (b * c₂) ∈ Ea Φ b := (Ea Φ b).mul_mem ((Ea Φ b).inv_mem hbE) hconj
    simpa using h1
  have h1 := hcen c₂ hc₂c hc₂E
  rw [hgb, h1, mul_one]

end Transfer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

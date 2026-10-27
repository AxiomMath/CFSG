module

public import CFSG.GF2Type.Smith1980Orth.W4SigmaEnd
public import CFSG.GF2Type.Smith1980Orth.W4SigmaLoc
public import CFSG.GF2Type.Smith1980Orth.W4SigmaQa
public import CFSG.GF2Type.Smith1980Orth.W4Pre
public import CFSG.GF2Type.Smith1980Orth.W4Irr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.GroupTheory.GLnTwoSplitting CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem W4Sigma.card_M_eq_card_QG_mul_card_Mbar (S : Setting G) :
    Nat.card S.M = Nat.card S.QG * Nat.card S.Mbar := by
  rw [card_eq_card_quotient_mul_card_subgroup S.ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange S.ρ).toEquiv, S.ker_ρ, mul_comm,
    S.card_QG_eq_card_Q]
  rfl

theorem OrthData.card_Mbar_le_of_width_eq_four (O : OrthData S) (hw : S.width = 4) :
    Nat.card S.Mbar ≤ 720 := by
  obtain ⟨h36, h60⟩ := O.card_omega_of_width_eq_four hw
  have hiso := O.card_isometries
  have hΩ : Nat.card (timmesfeldOmega O.q) ≤ 60 := by
    by_cases hp : timmesfeldPlusType O.q
    · rw [h36 hp]; norm_num
    · rw [h60 hp]
  rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
    omega
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin, hiso]
    norm_num
    omega

namespace S2Pre

variable (D : S2Pre S)

theorem eq_zero_or_eq_aV_of_pure {p s : Vt S D.g D.t} (hs : s ≠ 0)
    (h : D.coord (p, aV D.good.ht) = D.coord (s, 0) ∨ D.coord (p, aV D.good.ht) = D.coord (0, s) ∨
      D.coord (p, aV D.good.ht) = D.coord (s, s)) : p = 0 ∨ p = aV D.good.ht := by
  have ha := aV_ne_zero D.good.H D.good.ht
  rcases h with h | h | h <;> have h' := D.coord.injective h <;>
    simp only [Prod.mk.injEq] at h'
  · exact absurd h'.2 ha
  · exact Or.inl h'.1
  · exact Or.inr (h'.1.trans h'.2.symm)

theorem mem_V_of_sub (hw : S.width = 4)
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) {Z : Subgroup G}
    (hZQ : Z ≤ S.QG) (hZa : Z ≤ S.Qa D.g) (hZ8 : 8 < Nat.card Z)
    (hZc : ∀ y ∈ Z, y ≠ 1 → y ≠ S.z → IsConj S.z y) {y : G} (hy : y ∈ Z) :
    y ∈ V S D.g D.t := by
  classical
  set ã := aV D.good.ht with hã
  have ha0 : ã ≠ 0 := aV_ne_zero D.good.H D.good.ht
  have hcoord : ∀ w ∈ Z, ∃ p q : Vt S D.g D.t, S.cl w = D.coord (p, q) ∧
      D.betaV p ã = 0 ∧ (q = 0 ∨ q = ã) := by
    intro w hw'
    obtain ⟨⟨p, q⟩, hpq⟩ := D.coord.surjective (S.cl w)
    exact ⟨p, q, hpq.symm, (D.mem_Qa_iff_coord hw hP (hZQ hw') hpq.symm).mp (hZa hw')⟩
  have hne : ∀ w ∈ Z, S.cl w ≠ 0 → w ≠ 1 ∧ w ≠ S.z := fun w _ hw0 =>
    ⟨fun h1 => hw0 (by rw [h1, S.cl_one]), fun hz => hw0 (by rw [hz, S.cl_z])⟩
  have hpure : ∀ w ∈ Z, ∀ p : Vt S D.g D.t, S.cl w = D.coord (p, ã) → p = 0 ∨ p = ã := by
    intro w hwZ p hp
    have hw0 : S.cl w ≠ 0 := by
      rw [hp]
      intro h0
      have := D.coord.injective (h0.trans (map_zero D.coord).symm)
      exact ha0 (congrArg Prod.snd this)
    obtain ⟨h1, hz⟩ := hne w hwZ hw0
    obtain ⟨s, hs0, hs⟩ := D.exists_pure_of_isConj (hZQ hwZ) (hZc w hwZ h1 hz) hz
    rw [hp] at hs
    exact D.eq_zero_or_eq_aV_of_pure hs0 hs
  obtain ⟨p, q, hyc, hpβ, hq⟩ := hcoord y hy
  rcases hq with rfl | rfl
  · refine ⟨hZQ hy, ?_⟩
    rw [hyc, D.coord_apply_zero_right]
    exact p.2
  exfalso
  have hp := hpure y hy p hyc
  set F : Set S.Qt := {0, D.coord (ã, 0), D.coord (0, ã), D.coord (ã, ã)} with hF
  have hF4 : F.ncard ≤ 4 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  have hT : {w : G | w ∈ S.QG ∧ S.cl w ∈ F}.ncard < (Z : Set G).ncard := by
    have h1 : {w : G | w ∈ S.QG ∧ S.cl w ∈ F}.ncard = 2 * F.ncard := ncard_cl_preimage S F
    have h2 : (Z : Set G).ncard = Nat.card Z := (Nat.card_coe_set_eq _).symm
    rw [h1, h2]
    omega
  obtain ⟨y₂, hy₂Z, hy₂F⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hT (Set.toFinite _)
  have hy₂F' : S.cl y₂ ∉ F := fun h => hy₂F ⟨hZQ hy₂Z, h⟩
  obtain ⟨p₂, q₂, hy₂c, -, hq₂⟩ := hcoord y₂ hy₂Z
  have hq₂0 : q₂ = 0 := by
    rcases hq₂ with h | rfl
    · exact h
    · exfalso
      rcases hpure y₂ hy₂Z p₂ hy₂c with rfl | rfl
      · exact hy₂F' (by rw [hy₂c]; simp [hF])
      · exact hy₂F' (by rw [hy₂c]; simp [hF])
  subst hq₂0
  have hp₂ : p₂ ≠ 0 ∧ p₂ ≠ ã := by
    constructor
    · rintro rfl
      exact hy₂F' (by rw [hy₂c, Prod.mk_zero_zero, map_zero]; simp [hF])
    · rintro rfl
      exact hy₂F' (by rw [hy₂c]; simp [hF])
  have hprod : S.cl (y * y₂) = D.coord (p + p₂, ã) := by
    rw [S.cl_mul (hZQ hy) (hZQ hy₂Z), hyc, hy₂c, ← map_add, Prod.mk_add_mk, add_zero]
  rcases hpure _ (mul_mem hy hy₂Z) _ hprod with h | h <;> rcases hp with rfl | rfl
  · exact hp₂.1 (by simpa using h)
  · exact hp₂.2 (by
      calc p₂ = ã + (ã + p₂) := by rw [← add_assoc, two_add_self, zero_add]
        _ = ã := by rw [h, add_zero])
  · exact hp₂.2 (by simpa using h)
  · exact hp₂.1 (by
      calc p₂ = ã + (ã + p₂) := by rw [← add_assoc, two_add_self, zero_add]
        _ = 0 := by rw [h, two_add_self])

theorem card_V_inf_Qa (hw : S.width = 4)
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) :
    Nat.card (V S D.g D.t ⊓ S.Qa D.g : Subgroup G) = 16 := by
  set K0 : Submodule (ZMod 2) (Vt S D.g D.t) := LinearMap.ker (D.betaV (aV D.good.ht)) with hK0
  have hker : finrank (ZMod 2) K0 = 3 := by
    have hβ0 : D.betaV (aV D.good.ht) ≠ 0 := fun h0 =>
      aV_ne_zero D.good.H D.good.ht
        (D.betaV_nondegenerate.1 _ fun y => by rw [h0, LinearMap.zero_apply])
    have hrange : LinearMap.range (D.betaV (aV D.good.ht)) = ⊤ := by
      obtain ⟨y, hy⟩ : ∃ y, D.betaV (aV D.good.ht) y ≠ 0 := by
        by_contra h
        push Not at h
        exact hβ0 (LinearMap.ext h)
      have hy1 := OrthoF2.zmod2_eq_one_of_ne_zero hy
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (D.betaV (aV D.good.ht))
    rw [hrange, finrank_top, finrank_self, ← hK0, D.finrank_Vt, hw] at h1
    omega
  set W₀ : Submodule (ZMod 2) S.Qt := K0.map (Vt S D.g D.t).subtype with hW₀
  have hW : V S D.g D.t ⊓ S.Qa D.g = S.clPre W₀ := by
    ext y
    rw [Subgroup.mem_inf, D.mem_V_iff, S.mem_clPre]
    constructor
    · rintro ⟨⟨hyQ, hyV⟩, hya⟩
      have hc : S.cl y = D.coord (⟨S.cl y, hyV⟩, 0) :=
        (D.coord_apply_zero_right ⟨S.cl y, hyV⟩).symm
      obtain ⟨hβ, -⟩ := (D.mem_Qa_iff_coord hw hP hyQ hc).mp hya
      exact ⟨hyQ, ⟨S.cl y, hyV⟩, LinearMap.mem_ker.mpr ((D.betaV_symm _ _).trans hβ), rfl⟩
    · rintro ⟨hyQ, s, hs, hsy⟩
      have hyV : S.cl y ∈ Vt S D.g D.t := by rw [← hsy]; exact s.2
      refine ⟨⟨hyQ, hyV⟩, (D.mem_Qa_iff_coord hw hP hyQ (u := s) (v := 0) ?_).mpr
        ⟨(D.betaV_symm _ _).trans (LinearMap.mem_ker.mp hs), Or.inl rfl⟩⟩
      rw [D.coord_apply_zero_right]
      exact hsy.symm
  have hcardW : Nat.card W₀ = 8 := by
    have : Fintype K0 := Fintype.ofFinite _
    rw [hW₀, Nat.card_congr (Submodule.equivMapOfInjective _
      (Vt S D.g D.t).injective_subtype K0).toEquiv.symm, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ZMod 2), hker, ZMod.card]
    norm_num
  rw [hW, S.card_clPre, hcardW]

theorem ρ_eq_one_or_eq_t (hw : S.width = 4)
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) {y : G} (hyM : y ∈ S.M)
    (hya : y ∈ S.Qa D.g) (hcomm : ∀ v ∈ V S D.g D.t, v ∈ S.Qa D.g → y * v = v * y) :
    S.ρ ⟨y, hyM⟩ = 1 ∨ S.ρ ⟨y, hyM⟩ = D.t := by
  have hL : S.ρ ⟨y, hyM⟩ ∈ S.Lbar D.g := S.ρ_mem_Lbar ⟨hya, hyM⟩
  refine D.eq_one_or_eq_t_of_forall_fix hP hL fun s hs => ?_
  obtain ⟨v, hvQ, hv⟩ := S.exists_cl (s : S.Qt)
  have hvV : v ∈ V S D.g D.t := ⟨hvQ, by rw [hv]; exact s.2⟩
  have hva : v ∈ S.Qa D.g := (D.mem_Qa_iff_coord hw hP hvQ
    (by rw [D.coord_apply_zero_right, hv])).mpr ⟨hs, Or.inl rfl⟩
  rw [← hv, S.ρ_cl ⟨y, hyM⟩ hvQ]
  show S.cl (y * v * y⁻¹) = S.cl v
  rw [hcomm v hvV hva, mul_inv_cancel_right]

theorem false_of_pgl25Case (hw : S.width = 4)
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ)
    (hMbar : Nat.card S.Mbar ≤ 720) : False := by
  classical
  have haQ : D.g * S.z * D.g⁻¹ ∈ S.QG := D.good.H.conj_mem
  have hne : D.g * S.z * D.g⁻¹ ≠ S.z := D.good.H.conj_ne
  set V := V S D.g D.t with hV
  have hVQ : ∀ v ∈ V, v ∈ S.QG := fun v hv => ((D.mem_V_iff).mp hv).1
  have hzV : S.z ∈ V := S.z_mem_clPre _
  have haV : D.g * S.z * D.g⁻¹ ∈ V := D.a_mem_V
  have hzz := S.z_mul_z
  obtain ⟨u, -, hua, hau⟩ := S.exists_swap rfl haQ hne
  have hau' : u⁻¹ * S.z * u = D.g * S.z * D.g⁻¹ := by
    calc u⁻¹ * S.z * u = u⁻¹ * (u * (D.g * S.z * D.g⁻¹) * u⁻¹) * u := by rw [hau]
      _ = D.g * S.z * D.g⁻¹ := by group
  have hua' : u⁻¹ * (D.g * S.z * D.g⁻¹) * u = S.z := by
    calc u⁻¹ * (D.g * S.z * D.g⁻¹) * u = u⁻¹ * (u * S.z * u⁻¹) * u := by rw [hua]
      _ = S.z := by group
  have hK1 : ∀ y, y ∈ S.Qa D.g ↔ u⁻¹ * y * u ∈ S.QG := by
    intro y
    rw [Setting.Qa_eq_of_conj_eq S hua.symm, W4Sigma.mem_Qa_iff']
  have hK2 : ∀ y, y ∈ S.QG ↔ u⁻¹ * y * u ∈ S.Qa D.g := by
    intro y
    rw [Setting.Qa_eq_of_conj_eq S
      (show D.g * S.z * D.g⁻¹ = u⁻¹ * S.z * u⁻¹⁻¹ by rw [inv_inv, hau']), W4Sigma.mem_Qa_iff',
      inv_inv, show u * (u⁻¹ * y * u) * u⁻¹ = y by group]
  set Y : Subgroup G := V.map (MulAut.conj u).toMonoidHom with hY
  have hYmem : ∀ y, y ∈ Y ↔ u⁻¹ * y * u ∈ V := by
    intro y
    rw [hY, Subgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hv
    · intro hy
      exact ⟨u⁻¹ * y * u, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hYa : ∀ y ∈ Y, y ∈ S.Qa D.g := fun y hy =>
    (hK1 y).mpr (hVQ _ ((hYmem y).mp hy))
  have hYcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
    intro y hy y' hy'
    have h := D.V_comm ((hYmem y).mp hy) ((hYmem y').mp hy')
    have e : y * y' = u * ((u⁻¹ * y * u) * (u⁻¹ * y' * u)) * u⁻¹ := by group
    rw [e, h]
    group
  have hzY : S.z ∈ Y := (hYmem _).mpr (by rw [hau']; exact haV)
  have hYM : ∀ y ∈ Y, y ∈ S.M := fun y hy => S.mem_M_iff.mpr (hYcomm y hy _ hzY)
  have hYc : ∀ y ∈ Y, y ≠ 1 → IsConj S.z y := by
    intro y hy hy1
    have hv1 : u⁻¹ * y * u ≠ 1 := fun h => hy1 (by
      calc y = u * (u⁻¹ * y * u) * u⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hc := D.isConj_of_mem_V hP ((hYmem y).mp hy) hv1
    exact hc.trans (isConj_iff.mpr ⟨u, by group⟩)
  set V₀ : Subgroup G := V ⊓ S.Qa D.g with hV₀
  have hYQ : Y ⊓ S.QG = V₀.map (MulAut.conj u).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨u⁻¹ * y * u, ⟨(hYmem y).mp h1, (hK2 y).mp h2⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
      have e : u⁻¹ * ((MulAut.conj u).toMonoidHom v) * u = v := by
        simp [MulAut.conj_apply, mul_assoc]
      exact ⟨(hYmem _).mpr (by rw [e]; exact hv1), (hK2 _).mpr (by rw [e]; exact hv2)⟩
  have hcardYQ : Nat.card (Y ⊓ S.QG : Subgroup G) = Nat.card V₀ := by
    rw [hYQ]
    exact Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hcardV₀ : Nat.card V₀ = 16 := D.card_V_inf_Qa hw hP
  have hYQV : ∀ y ∈ Y ⊓ S.QG, y ∈ V := fun y hy =>
    D.mem_V_of_sub hw hP (Z := Y ⊓ S.QG) inf_le_right (fun y hy => hYa y hy.1)
      (by rw [hcardYQ, hcardV₀]; norm_num) (fun y hy hy1 _ => hYc y hy.1 hy1) hy
  have hYQeq : Y ⊓ S.QG = V₀ := by
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ⟨hYQV y hy, hYa y hy.1⟩) ?_
    rw [hcardYQ]
  have hV₀Y : ∀ v ∈ V₀, v ∈ Y := fun v hv => by
    rw [← hYQeq] at hv
    exact hv.1
  have hYρ : ∀ y (hy : y ∈ Y), S.ρ ⟨y, hYM y hy⟩ = 1 ∨ S.ρ ⟨y, hYM y hy⟩ = D.t := by
    intro y hy
    exact D.ρ_eq_one_or_eq_t hw hP (hYM y hy) (hYa y hy) fun v hvV hva =>
      hYcomm y hy v (hV₀Y v ⟨hvV, hva⟩)
  obtain ⟨v₀, hv₀V, hv₀a⟩ : ∃ v ∈ V, v ∉ S.Qa D.g := by
    by_contra hcon
    push Not at hcon
    exact D.good.hVQ fun v hv => hcon v hv
  obtain ⟨x, hx⟩ : ∃ x : G, x = u * v₀ * u⁻¹ := ⟨_, rfl⟩
  have hxv : u⁻¹ * x * u = v₀ := by rw [hx]; group
  have hxY : x ∈ Y := (hYmem x).mpr (by rw [hxv]; exact hv₀V)
  have hxQ : x ∉ S.QG := fun h => hv₀a (by
    have := (hK2 x).mp h
    rwa [hxv] at this)
  have hxM : x ∈ S.M := hYM x hxY
  have hxt : S.ρ ⟨x, hxM⟩ = D.t := by
    rcases hYρ x hxY with h | h
    · exact absurd ((S.ρ_eq_one_iff _).mp h) hxQ
    · exact h
  have hxx : x * x = 1 := by
    have h := D.V_mul_self hv₀V
    calc x * x = u * (v₀ * v₀) * u⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h]; group
  have hxV : ∀ v ∈ V, x * v = v * x := fun v hv => D.comm_of_ρ_eq_t hxM hxt hxx hv
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  set A : Subgroup G := centralizer (V : Set G) ⊓ S.M with hA
  have hρmul : ∀ (b : G) (hb : b ∈ S.M), S.ρ ⟨x * b, mul_mem hxM hb⟩ = D.t * S.ρ ⟨b, hb⟩ := by
    intro b hb
    rw [← hxt, ← map_mul]
    rfl
  have hAmem : ∀ b, b ∈ A ↔ b ∈ V ∨ x * b ∈ V := by
    intro b
    constructor
    · rintro ⟨hbC, hbM⟩
      have hcomm : ∀ v ∈ V, b * v = v * b := fun v hv =>
        (Subgroup.mem_centralizer_iff.mp hbC v hv).symm
      have hfix : ∀ s ∈ Vt S D.g D.t,
          ((S.ρ ⟨b, hbM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) s = s := by
        intro s hs
        obtain ⟨v, hvQ, rfl⟩ := S.exists_cl s
        have hvV : v ∈ V := ⟨hvQ, hs⟩
        rw [S.ρ_cl ⟨b, hbM⟩ hvQ]
        show S.cl (b * v * b⁻¹) = S.cl v
        rw [hcomm v hvV, mul_inv_cancel_right]
      rcases D.eq_one_or_eq_t_of_fix_Vt ⟨⟨b, hbM⟩, rfl⟩ hfix with h | h
      · exact Or.inl (D.mem_V_of_comm ((S.ρ_eq_one_iff _).mp h) hcomm)
      · right
        have hxbQ : x * b ∈ S.QG := (S.ρ_eq_one_iff ⟨x * b, mul_mem hxM hbM⟩).mp (by
          rw [hρmul b hbM, h, D.t_mul_t])
        refine D.mem_V_of_comm hxbQ fun v hv => ?_
        rw [mul_assoc, hcomm v hv, ← mul_assoc, hxV v hv, mul_assoc]
    · rintro (h | h)
      · exact ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => D.V_comm hv h,
          S.QG_le_M (hVQ b h)⟩
      · have hb : b = x * (x * b) := by rw [← mul_assoc, hxx, one_mul]
        refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, ?_⟩
        · rw [hb, ← mul_assoc, ← hxV v hv, mul_assoc, D.V_comm hv h, ← mul_assoc]
        · rw [hb]
          exact mul_mem hxM (S.QG_le_M (hVQ _ h))
  have hAx : ∀ b ∈ A, b * x = x * b := by
    intro b hb
    rcases (hAmem b).mp hb with h | h
    · exact (hxV b h).symm
    · have hw := hxV (x * b) h
      calc b * x = x * (x * b * x) := by rw [← mul_assoc, ← mul_assoc, hxx, one_mul]
        _ = x * (x * (x * b)) := by rw [← hw]
        _ = x * b := by rw [← mul_assoc x x, hxx, one_mul]
  have hAcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := by
    intro b hb c hc
    have hbV : ∀ v ∈ V, b * v = v * b := fun v hv =>
      (Subgroup.mem_centralizer_iff.mp hb.1 v hv).symm
    rcases (hAmem c).mp hc with h | h
    · exact hbV c h
    · have hc' : c = x * (x * c) := by rw [← mul_assoc, hxx, one_mul]
      rw [hc', ← mul_assoc, hAx b hb, mul_assoc, hbV _ h, ← mul_assoc]
  have hAtwo : ∀ b ∈ A, b * b = 1 := by
    intro b hb
    rcases (hAmem b).mp hb with h | h
    · exact D.V_mul_self h
    · have hb' : b = x * (x * b) := by rw [← mul_assoc, hxx, one_mul]
      have hw := D.V_mul_self h
      have hxw := hxV (x * b) h
      calc b * b = x * (x * b) * (x * (x * b)) := by rw [← hb']
        _ = x * ((x * b) * x) * (x * b) := by group
        _ = x * (x * (x * b)) * (x * b) := by rw [← hxw]
        _ = (x * x) * ((x * b) * (x * b)) := by group
        _ = 1 := by rw [hxx, hw, one_mul]
  obtain ⟨eA, heA⟩ : ∃ e : W4Sigma.ElemAb G, e.E = A := ⟨⟨A, hAcomm, hAtwo⟩, rfl⟩
  obtain ⟨eV, heV⟩ : ∃ e : W4Sigma.ElemAb G, e.E = V :=
    ⟨⟨V, fun _ ha _ hb => D.V_comm ha hb, fun _ ha => D.V_mul_self ha⟩, rfl⟩
  have heVmem : ∀ v : eV.E, (v : G) ∈ V := fun v => heV ▸ v.2
  have hzeV : S.z ∈ eV.E := heV ▸ hzV
  have hVA : V ≤ A := fun v hv => (hAmem v).mpr (Or.inl hv)
  have hxA : x ∈ A := (hAmem x).mpr (Or.inr (by rw [hxx]; exact one_mem _))
  have hxnV : x ∉ V := fun h => hxQ (hVQ x h)
  have hAQ : ∀ b ∈ A, b ∈ S.QG ↔ b ∈ V := by
    intro b hb
    refine ⟨fun hbQ => ?_, fun h => hVQ b h⟩
    rcases (hAmem b).mp hb with h | h
    · exact h
    · exfalso
      apply hxQ
      have e : x = (x * b) * b⁻¹ := by group
      rw [e]
      exact mul_mem (hVQ _ h) (inv_mem hbQ)
  have hcardA : Nat.card A = 64 := by
    have hAset : (A : Set G) = (V : Set G) ∪ (fun v => x * v) '' (V : Set G) := by
      ext b
      simp only [SetLike.mem_coe, Set.mem_union, Set.mem_image]
      rw [hAmem]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨x * b, h, by rw [← mul_assoc, hxx, one_mul]⟩
      · rintro (h | ⟨v, hv, rfl⟩)
        · exact Or.inl h
        · right
          rw [← mul_assoc, hxx, one_mul]
          exact hv
    have hdisj : Disjoint (V : Set G) ((fun v => x * v) '' (V : Set G)) := by
      rw [Set.disjoint_left]
      rintro b hb ⟨v, hv, rfl⟩
      apply hxQ
      have e : x = (x * v) * v⁻¹ := by group
      rw [e]
      exact mul_mem (hVQ _ hb) (inv_mem (hVQ _ hv))
    have hV32 : (V : Set G).ncard = 32 := by
      rw [← Nat.card_coe_set_eq]
      exact D.card_V hw
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hAset, Set.ncard_union_eq hdisj,
      Set.ncard_image_of_injective _ (mul_right_injective x), hV32]
  have hYA : ∀ y ∈ Y, y ∈ A := by
    intro y hy
    rcases hYρ y hy with h | h
    · have hyQ : y ∈ S.QG := (S.ρ_eq_one_iff _).mp h
      exact hVA (hYQV y ⟨hy, hyQ⟩)
    · have hxyQ : x * y ∈ S.QG := (S.ρ_eq_one_iff ⟨x * y, mul_mem hxM (hYM y hy)⟩).mp (by
        rw [hρmul y (hYM y hy), h, D.t_mul_t])
      exact (hAmem y).mpr (Or.inr (hYQV _ ⟨mul_mem hxY hy, hxyQ⟩))
  have hconjA : ∀ b ∈ A, u⁻¹ * b * u ∈ A := by
    intro b hb
    have hbV : ∀ v ∈ V, v * b = b * v := fun v hv => Subgroup.mem_centralizer_iff.mp hb.1 v hv
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, S.mem_M_iff.mpr ?_⟩
    · have e : u⁻¹ * (u * v * u⁻¹) * u = v := by group
      have hvY : u * v * u⁻¹ ∈ Y := (hYmem _).mpr (by rw [e]; exact hv)
      have h := hAcomm b hb _ (hYA _ hvY)
      calc v * (u⁻¹ * b * u) = u⁻¹ * ((u * v * u⁻¹) * b) * u := by group
        _ = u⁻¹ * (b * (u * v * u⁻¹)) * u := by rw [h]
        _ = u⁻¹ * b * u * v := by group
    · have h := hbV _ haV
      have e1 : u⁻¹ * b * u * S.z = u⁻¹ * (b * (D.g * S.z * D.g⁻¹)) * u := by
        conv_lhs => rw [← hua']
        group
      have e2 : S.z * (u⁻¹ * b * u) = u⁻¹ * ((D.g * S.z * D.g⁻¹) * b) * u := by
        conv_lhs => rw [← hua']
        group
      rw [e1, e2, h]
  have hu : u ∈ normalizer (A : Set G) := by
    let f : A → A := fun b => ⟨u⁻¹ * b * u, hconjA b b.2⟩
    have hf : Function.Injective f := fun b c h => Subtype.ext (by
      have h' : u⁻¹ * (b : G) * u = u⁻¹ * c * u := congrArg Subtype.val h
      simpa using h')
    have hfs := Finite.injective_iff_surjective.mp hf
    have hu' : u⁻¹ ∈ normalizer (A : Set G) := by
      refine mem_normalizer_iff.mpr fun b => ⟨fun hb => by
        rw [inv_inv]; exact hconjA b hb, fun hb => ?_⟩
      rw [inv_inv] at hb
      obtain ⟨c, hc⟩ := hfs ⟨_, hb⟩
      have h' : u⁻¹ * (c : G) * u = u⁻¹ * b * u := congrArg Subtype.val hc
      have hcb : (c : G) = b := by simpa using h'
      rw [← hcb]
      exact c.2
    simpa using inv_mem hu'
  have hNA : ∀ g ∈ S.M, g ∈ normalizer (V : Set G) → g ∈ normalizer (A : Set G) := by
    intro g hgM hgN
    have hgN' : g⁻¹ ∈ normalizer (V : Set G) := inv_mem hgN
    refine mem_normalizer_iff.mpr fun b => ?_
    constructor
    · rintro ⟨hbC, hbM⟩
      have hgbM : g * b * g⁻¹ ∈ S.M := mul_mem (mul_mem hgM hbM) (inv_mem hgM)
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, hgbM⟩
      have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V := (mem_normalizer_iff.mp hgN' v).mp hv
      rw [inv_inv] at hv'
      have h := Subgroup.mem_centralizer_iff.mp hbC _ hv'
      calc v * (g * b * g⁻¹) = g * ((g⁻¹ * v * g) * b) * g⁻¹ := by group
        _ = g * (b * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
        _ = g * b * g⁻¹ * v := by group
    · rintro ⟨hbC, hbM⟩
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => ?_, ?_⟩
      · have hv' : g * v * g⁻¹ ∈ V := (mem_normalizer_iff.mp hgN v).mp hv
        have h := Subgroup.mem_centralizer_iff.mp hbC _ hv'
        calc v * b = g⁻¹ * ((g * v * g⁻¹) * (g * b * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * b * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h]
          _ = b * v := by group
      · have := mul_mem (mul_mem (inv_mem hgM) hbM) (inv_mem (inv_mem hgM))
        simpa [mul_assoc] using this
  have hQN : S.QG ≤ normalizer (A : Set G) := by
    intro q hq
    refine hNA q (S.QG_le_M hq) (mem_normalizer_iff.mpr fun v => ?_)
    have hcl : ∀ w ∈ S.QG, S.cl (q * w * q⁻¹) = S.cl w := fun w hw => by
      rw [← S.ρ_cl ⟨q, S.QG_le_M hq⟩ hw, (S.ρ_eq_one_iff _).mpr hq]
      rfl
    constructor
    · intro hv
      exact ⟨S.conj_mem_QG (S.QG_le_M hq) (hVQ v hv), by rw [hcl v (hVQ v hv)]; exact hv.2⟩
    · intro hv
      have hvQ : v ∈ S.QG := by
        have := S.conj_mem_QG (inv_mem (S.QG_le_M hq)) hv.1
        simpa [mul_assoc] using this
      exact ⟨hvQ, by rw [← hcl v hvQ]; exact hv.2⟩
  have htrans : ∀ v ∈ V, ∀ w ∈ V, v ≠ 1 → v ≠ S.z → w ≠ 1 → w ≠ S.z →
      ∃ g ∈ normalizer (A : Set G), g ∈ S.M ∧ g * v * g⁻¹ = w := by
    intro v hv w hw' hv1 hvz hw1 hwz
    obtain ⟨m, hmM, hmN, hm⟩ := D.exists_conj_eq_of_mem_V hP hv hw' hv1 hvz hw1 hwz
    exact ⟨m, hNA m hmM hmN, hmM, hm⟩
  have hsurj : ∀ v ∈ V, ∃ q ∈ S.QG, q * x * q⁻¹ = x * v ∨ q * x * q⁻¹ = x * v * S.z := by
    intro v hv
    obtain ⟨q, hq, hcl⟩ := D.exists_cl_comm_eq hxM hxt hv
    have hcQ : q * x * q⁻¹ * x⁻¹ ∈ S.QG := by
      rw [show q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) by group]
      exact mul_mem hq (S.conj_mem_QG hxM (inv_mem hq))
    have hxz : x * S.z = S.z * x := S.z_comm hxM
    refine ⟨q, hq, ?_⟩
    have e : q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
    rcases (S.cl_eq_cl_iff (hVQ v hv) hcQ).mp hcl.symm with h | h
    · left
      rw [e, h, hxV v hv]
    · right
      rw [e, h, mul_assoc, ← hxz, ← mul_assoc, hxV v hv]
  have htransv : ∀ f : Module.Dual (ZMod 2) (Additive eV.E),
      f (W4Sigma.ElemAb.vec (⟨S.z, hzeV⟩ : eV.E)) = 0 →
        ∃ q ∈ S.QG, ∀ v : eV.E, q * (v : G) = v * q ↔ f (W4Sigma.ElemAb.vec v) = 0 := by
    intro f hf
    let π₀ : Additive eV.E →+ Vt S D.g D.t :=
      { toFun := fun a => ⟨S.cl ((Additive.toMul a : eV.E) : G),
          ((D.mem_V_iff).mp (heVmem (Additive.toMul a))).2⟩
        map_zero' := Subtype.ext S.cl_one
        map_add' := fun a b => Subtype.ext (S.cl_mul (hVQ _ (heVmem (Additive.toMul a)))
          (hVQ _ (heVmem (Additive.toMul b)))) }
    let π : Additive eV.E →ₗ[ZMod 2] Vt S D.g D.t := π₀.toZModLinearMap 2
    have hπ : ∀ v : eV.E,
        π (W4Sigma.ElemAb.vec v) = ⟨S.cl v, ((D.mem_V_iff).mp (heVmem v)).2⟩ := fun _ => rfl
    have hπs : Function.Surjective π := by
      intro s
      obtain ⟨v, hvQ, hv⟩ := S.exists_cl (s : S.Qt)
      have hvV : v ∈ eV.E := heV ▸ (⟨hvQ, by rw [hv]; exact s.2⟩ : v ∈ V)
      exact ⟨W4Sigma.ElemAb.vec (⟨v, hvV⟩ : eV.E), Subtype.ext hv⟩
    have hker : LinearMap.ker π ≤ LinearMap.ker f := by
      intro a ha
      obtain ⟨v, rfl⟩ := W4Sigma.ElemAb.exists_vec a
      have h0 : S.cl (v : G) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp ha)
      rw [LinearMap.mem_ker]
      rcases (S.cl_eq_zero_iff (hVQ _ (heVmem v))).mp h0 with h | h
      · rw [W4Sigma.ElemAb.vec_eq_zero_iff.mpr h, map_zero]
      · rw [show W4Sigma.ElemAb.vec v = W4Sigma.ElemAb.vec (⟨S.z, hzeV⟩ : eV.E) from
          W4Sigma.ElemAb.vec_eq_vec_iff.mpr h]
        exact hf
    let φ : Vt S D.g D.t →ₗ[ZMod 2] ZMod 2 :=
      ((LinearMap.ker π).liftQ f hker).comp
        (π.quotKerEquivOfSurjective hπs).symm.toLinearMap
    have hφ : ∀ a, φ (π a) = f a := by
      intro a
      show (LinearMap.ker π).liftQ f hker ((π.quotKerEquivOfSurjective hπs).symm (π a)) = f a
      rw [show (π.quotKerEquivOfSurjective hπs).symm (π a) = Submodule.Quotient.mk a by
        rw [LinearEquiv.symm_apply_eq]; rfl]
      rfl
    obtain ⟨q, hq, hqφ⟩ := D.exists_comm_iff φ
    refine ⟨q, hq, fun v => ?_⟩
    rw [hqφ v (heVmem v), ← hφ (W4Sigma.ElemAb.vec v), hπ v]
  have hcardM : Nat.card S.M ≤ 368640 := by
    rw [W4Sigma.card_M_eq_card_QG_mul_card_Mbar S, S.card_QG_eq_card_Q, S.card_Q_eq, hw]
    omega
  exact W4Sigma.SigmaEnd.false (S := S) (A := eA) (V := eV) (x := x) (u := u)
    { V_le := by rw [heV, heA]; exact hVA
      card_A := by rw [heA]; exact hcardA
      card_V := by rw [heV]; exact D.card_V hw
      z_mem := hzeV
      mem_QG_iff := by rw [heA, heV]; exact hAQ
      x_mem := by rw [heA]; exact hxA
      x_not_mem := by rw [heV]; exact hxnV
      u_mem := by rw [heA]; exact hu
      u_conj_mem := by rw [heV, hua]; exact haV
      u_conj_ne := by rw [hua]; exact hne
      QG_le := by rw [heA]; exact hQN
      trans := by rw [heA, heV]; exact htrans
      surj := by rw [heV]; exact hsurj
      cent_le := by rw [heV]; exact fun q hq hc => D.mem_V_of_comm hq hc
      transv := htransv
      card_M := hcardM }

end S2Pre

theorem W4.pgl25W4Free : W4.PGL25W4Free := by
  intro G _ _ _ S O hw _ hirr hnoAll g H hNo C t k ht ht1 hVQ hkM hk1 hk3 htk hdec hR hN hP
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have hP3 : Nat.card (zpowers k) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hk3 hk1]
  have hPn : ∀ m ∈ S.Mbar, ∀ p ∈ zpowers k, m * p * m⁻¹ ∈ zpowers k := by
    intro m hm p hp
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hp
    rw [← conj_zpow]
    rcases W4.conj_k_cases htt hk3 htk hdec hm with h | h
    · rw [h]
      exact zpow_mem (mem_zpowers k) n
    · rw [h]
      exact zpow_mem (inv_mem (mem_zpowers k)) n
  have hP1k : zpowers k ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hP3
    omega
  have hfpf : S13.FixFree S (zpowers k) := S13.fixFree_of hP1k hPn hirr
  let D : S2Pre S := ⟨g, t, k, ⟨H, hNo, C, ht, ht1, hR, hVQ, hN, hirr, hnoAll⟩, by omega,
    by rw [hP.finrank_eq, hw], hkM, hk1, hk3, fun x hx => W4.conj_k_cases htt hk3 htk hdec hx, htk,
    fun v hv => S13.fix_eq_zero hP3 hfpf (mem_zpowers k) hk1 v hv, hdec, S2Rel.full hkM⟩
  exact D.false_of_pgl25Case hw hP (O.card_Mbar_le_of_width_eq_four hw)

end CFSG.GF2Type.Smith1980Orth
